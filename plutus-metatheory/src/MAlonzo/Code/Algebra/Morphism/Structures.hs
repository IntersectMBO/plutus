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

module MAlonzo.Code.Algebra.Morphism.Structures where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Relation.Binary.Morphism.Structures

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
d_Carrier_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 -> ()
d_Carrier_34 = erased
-- Algebra.Morphism.Structures.SuccessorSetMorphisms._.suc#
d_suc'35'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  AgdaAny -> AgdaAny
d_suc'35'_38 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_suc'35'_38 v4
du_suc'35'_38 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  AgdaAny -> AgdaAny
du_suc'35'_38 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_suc'35'_28 (coe v0)
-- Algebra.Morphism.Structures.SuccessorSetMorphisms._.zero#
d_zero'35'_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 -> AgdaAny
d_zero'35'_40 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_zero'35'_40 v4
du_zero'35'_40 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 -> AgdaAny
du_zero'35'_40 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_zero'35'_30 (coe v0)
-- Algebra.Morphism.Structures.SuccessorSetMorphisms._.Homomorphic₀
d_Homomorphic'8320'_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_58 = erased
-- Algebra.Morphism.Structures.SuccessorSetMorphisms._.Homomorphic₁
d_Homomorphic'8321'_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_60 = erased
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetHomomorphism
d_IsSuccessorSetHomomorphism_68 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSuccessorSetHomomorphism_68
  = C_constructor_84 MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
                     (AgdaAny -> AgdaAny) AgdaAny
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetHomomorphism.isRelHomomorphism
d_isRelHomomorphism_78 ::
  T_IsSuccessorSetHomomorphism_68 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_78 v0
  = case coe v0 of
      C_constructor_84 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetHomomorphism.suc#-homo
d_suc'35''45'homo_80 ::
  T_IsSuccessorSetHomomorphism_68 -> AgdaAny -> AgdaAny
d_suc'35''45'homo_80 v0
  = case coe v0 of
      C_constructor_84 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetHomomorphism.zero#-homo
d_zero'35''45'homo_82 :: T_IsSuccessorSetHomomorphism_68 -> AgdaAny
d_zero'35''45'homo_82 v0
  = case coe v0 of
      C_constructor_84 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism
d_IsSuccessorSetMonomorphism_88 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSuccessorSetMonomorphism_88
  = C_constructor_110 T_IsSuccessorSetHomomorphism_68
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism.isSuccessorSetHomomorphism
d_isSuccessorSetHomomorphism_96 ::
  T_IsSuccessorSetMonomorphism_88 -> T_IsSuccessorSetHomomorphism_68
d_isSuccessorSetHomomorphism_96 v0
  = case coe v0 of
      C_constructor_110 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism.injective
d_injective_98 ::
  T_IsSuccessorSetMonomorphism_88 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_98 v0
  = case coe v0 of
      C_constructor_110 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_102 ::
  T_IsSuccessorSetMonomorphism_88 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_102 v0
  = coe
      d_isRelHomomorphism_78
      (coe d_isSuccessorSetHomomorphism_96 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism._.suc#-homo
d_suc'35''45'homo_104 ::
  T_IsSuccessorSetMonomorphism_88 -> AgdaAny -> AgdaAny
d_suc'35''45'homo_104 v0
  = coe
      d_suc'35''45'homo_80 (coe d_isSuccessorSetHomomorphism_96 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism._.zero#-homo
d_zero'35''45'homo_106 ::
  T_IsSuccessorSetMonomorphism_88 -> AgdaAny
d_zero'35''45'homo_106 v0
  = coe
      d_zero'35''45'homo_82
      (coe d_isSuccessorSetHomomorphism_96 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetMonomorphism.isRelMonomorphism
d_isRelMonomorphism_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSuccessorSetMonomorphism_88 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_108 v7
du_isRelMonomorphism_108 ::
  T_IsSuccessorSetMonomorphism_88 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_108 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_constructor_86
      (coe
         d_isRelHomomorphism_78
         (coe d_isSuccessorSetHomomorphism_96 (coe v0)))
      (coe d_injective_98 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism
d_IsSuccessorSetIsomorphism_114 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSuccessorSetIsomorphism_114
  = C_constructor_142 T_IsSuccessorSetMonomorphism_88
                      (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism.isSuccessorSetMonomorphism
d_isSuccessorSetMonomorphism_122 ::
  T_IsSuccessorSetIsomorphism_114 -> T_IsSuccessorSetMonomorphism_88
d_isSuccessorSetMonomorphism_122 v0
  = case coe v0 of
      C_constructor_142 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism.surjective
d_surjective_124 ::
  T_IsSuccessorSetIsomorphism_114 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_124 v0
  = case coe v0 of
      C_constructor_142 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.injective
d_injective_128 ::
  T_IsSuccessorSetIsomorphism_114 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_128 v0
  = coe
      d_injective_98 (coe d_isSuccessorSetMonomorphism_122 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_130 ::
  T_IsSuccessorSetIsomorphism_114 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_130 v0
  = coe
      d_isRelHomomorphism_78
      (coe
         d_isSuccessorSetHomomorphism_96
         (coe d_isSuccessorSetMonomorphism_122 (coe v0)))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSuccessorSetIsomorphism_114 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_132 v7
du_isRelMonomorphism_132 ::
  T_IsSuccessorSetIsomorphism_114 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_132 v0
  = coe
      du_isRelMonomorphism_108
      (coe d_isSuccessorSetMonomorphism_122 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.isSuccessorSetHomomorphism
d_isSuccessorSetHomomorphism_134 ::
  T_IsSuccessorSetIsomorphism_114 -> T_IsSuccessorSetHomomorphism_68
d_isSuccessorSetHomomorphism_134 v0
  = coe
      d_isSuccessorSetHomomorphism_96
      (coe d_isSuccessorSetMonomorphism_122 (coe v0))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.suc#-homo
d_suc'35''45'homo_136 ::
  T_IsSuccessorSetIsomorphism_114 -> AgdaAny -> AgdaAny
d_suc'35''45'homo_136 v0
  = coe
      d_suc'35''45'homo_80
      (coe
         d_isSuccessorSetHomomorphism_96
         (coe d_isSuccessorSetMonomorphism_122 (coe v0)))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism._.zero#-homo
d_zero'35''45'homo_138 ::
  T_IsSuccessorSetIsomorphism_114 -> AgdaAny
d_zero'35''45'homo_138 v0
  = coe
      d_zero'35''45'homo_82
      (coe
         d_isSuccessorSetHomomorphism_96
         (coe d_isSuccessorSetMonomorphism_122 (coe v0)))
-- Algebra.Morphism.Structures.SuccessorSetMorphisms.IsSuccessorSetIsomorphism.isRelIsomorphism
d_isRelIsomorphism_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSuccessorSet_10 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSuccessorSetIsomorphism_114 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_140 v7
du_isRelIsomorphism_140 ::
  T_IsSuccessorSetIsomorphism_114 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_140 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_constructor_124
      (coe
         du_isRelMonomorphism_108
         (coe d_isSuccessorSetMonomorphism_122 (coe v0)))
      (coe d_surjective_124 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms._._∙_
d__'8729'__160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__160 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8729'__160 v4
du__'8729'__160 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8729'__160 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__60 (coe v0)
-- Algebra.Morphism.Structures.MagmaMorphisms._._≈_
d__'8776'__162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__162 = erased
-- Algebra.Morphism.Structures.MagmaMorphisms._.Carrier
d_Carrier_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 -> ()
d_Carrier_166 = erased
-- Algebra.Morphism.Structures.MagmaMorphisms._.Homomorphic₂
d_Homomorphic'8322'_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_188 = erased
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaHomomorphism
d_IsMagmaHomomorphism_194 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMagmaHomomorphism_194
  = C_constructor_210 MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
                      (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_202 ::
  T_IsMagmaHomomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_202 v0
  = case coe v0 of
      C_constructor_210 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaHomomorphism.homo
d_homo_204 ::
  T_IsMagmaHomomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_204 v0
  = case coe v0 of
      C_constructor_210 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaHomomorphism._.cong
d_cong_208 ::
  T_IsMagmaHomomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_208 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism
d_IsMagmaMonomorphism_214 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMagmaMonomorphism_214
  = C_constructor_236 T_IsMagmaHomomorphism_194
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_222 ::
  T_IsMagmaMonomorphism_214 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_222 v0
  = case coe v0 of
      C_constructor_236 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism.injective
d_injective_224 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_224 v0
  = case coe v0 of
      C_constructor_236 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism._.homo
d_homo_228 ::
  T_IsMagmaMonomorphism_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_228 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_230 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_230 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism._.cong
d_cong_232 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_234 v7
du_isRelMonomorphism_234 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_234 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_constructor_86
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
      (coe d_injective_224 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism
d_IsMagmaIsomorphism_240 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMagmaIsomorphism_240
  = C_constructor_268 T_IsMagmaMonomorphism_214
                      (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_248 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_248 v0
  = case coe v0 of
      C_constructor_268 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism.surjective
d_surjective_250 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_250 v0
  = case coe v0 of
      C_constructor_268 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.homo
d_homo_254 ::
  T_IsMagmaIsomorphism_240 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_254 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.injective
d_injective_256 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_256 v0
  = coe d_injective_224 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_258 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_258 v0
  = coe
      d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_260 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_260 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_262 v7
du_isRelMonomorphism_262 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_262 v0
  = coe
      du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism._.cong
d_cong_264 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_264 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_222
            (coe d_isMagmaMonomorphism_248 (coe v0))))
-- Algebra.Morphism.Structures.MagmaMorphisms.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_266 v7
du_isRelIsomorphism_266 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_266 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_constructor_124
      (coe
         du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0)))
      (coe d_surjective_250 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._._≈_
d__'8776'__288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__288 = erased
-- Algebra.Morphism.Structures.MonoidMorphisms._.Carrier
d_Carrier_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 -> ()
d_Carrier_292 = erased
-- Algebra.Morphism.Structures.MonoidMorphisms._.ε
d_ε_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 -> AgdaAny
d_ε_296 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_ε_296 v4
du_ε_296 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 -> AgdaAny
du_ε_296 v0 = coe MAlonzo.Code.Algebra.Bundles.Raw.d_ε_94 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.Homomorphic₀
d_Homomorphic'8320'_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_314 = erased
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaHomomorphism
d_IsMagmaHomomorphism_324 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism
d_IsMagmaIsomorphism_328 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism
d_IsMagmaMonomorphism_332 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaHomomorphism.homo
d_homo_338 ::
  T_IsMagmaHomomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_338 v0 = coe d_homo_204 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_340 ::
  T_IsMagmaHomomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_340 v0 = coe d_isRelHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaHomomorphism.cong
d_cong_342 ::
  T_IsMagmaHomomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_342 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.homo
d_homo_346 ::
  T_IsMagmaIsomorphism_240 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_346 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.injective
d_injective_348 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_348 v0
  = coe d_injective_224 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_350 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_350 v0
  = coe
      d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_352 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_352 v0
  = coe d_isMagmaMonomorphism_248 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_354 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_354 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_356
du_isRelIsomorphism_356 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_356 v0 v1 = coe du_isRelIsomorphism_266 v1
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_358 v7
du_isRelMonomorphism_358 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_358 v0
  = coe
      du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.surjective
d_surjective_360 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_360 v0 = coe d_surjective_250 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaIsomorphism.cong
d_cong_362 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_362 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_222
            (coe d_isMagmaMonomorphism_248 (coe v0))))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.homo
d_homo_366 ::
  T_IsMagmaMonomorphism_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_366 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.injective
d_injective_368 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_368 v0 = coe d_injective_224 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_370 ::
  T_IsMagmaMonomorphism_214 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_370 v0
  = coe d_isMagmaHomomorphism_222 (coe v0)
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_372 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_372 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_374
du_isRelMonomorphism_374 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_374 v0 v1 = coe du_isRelMonomorphism_234 v1
-- Algebra.Morphism.Structures.MonoidMorphisms._.IsMagmaMonomorphism.cong
d_cong_376 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_376 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism
d_IsMonoidHomomorphism_380 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMonoidHomomorphism_380
  = C_constructor_400 T_IsMagmaHomomorphism_194 AgdaAny
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_388 ::
  T_IsMonoidHomomorphism_380 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_388 v0
  = case coe v0 of
      C_constructor_400 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism.ε-homo
d_ε'45'homo_390 :: T_IsMonoidHomomorphism_380 -> AgdaAny
d_ε'45'homo_390 v0
  = case coe v0 of
      C_constructor_400 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism._.homo
d_homo_394 ::
  T_IsMonoidHomomorphism_380 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_394 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_388 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_396 ::
  T_IsMonoidHomomorphism_380 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_396 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_388 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidHomomorphism._.cong
d_cong_398 ::
  T_IsMonoidHomomorphism_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_398 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_388 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism
d_IsMonoidMonomorphism_404 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMonoidMonomorphism_404
  = C_constructor_434 T_IsMonoidHomomorphism_380
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_412 ::
  T_IsMonoidMonomorphism_404 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_412 v0
  = case coe v0 of
      C_constructor_434 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism.injective
d_injective_414 ::
  T_IsMonoidMonomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_414 v0
  = case coe v0 of
      C_constructor_434 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.homo
d_homo_418 ::
  T_IsMonoidMonomorphism_404 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_418 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_420 ::
  T_IsMonoidMonomorphism_404 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_420 v0
  = coe
      d_isMagmaHomomorphism_388 (coe d_isMonoidHomomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_422 ::
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_422 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.ε-homo
d_ε'45'homo_424 :: T_IsMonoidMonomorphism_404 -> AgdaAny
d_ε'45'homo_424 v0
  = coe d_ε'45'homo_390 (coe d_isMonoidHomomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.cong
d_cong_426 ::
  T_IsMonoidMonomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_426 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_isMonoidHomomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_428 v7
du_isMagmaMonomorphism_428 ::
  T_IsMonoidMonomorphism_404 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_428 v0
  = coe
      C_constructor_236
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_412 (coe v0)))
      (coe d_injective_414 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_432 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_432 v7
du_isRelMonomorphism_432 ::
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_432 v0
  = coe
      du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism
d_IsMonoidIsomorphism_438 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMonoidIsomorphism_438
  = C_constructor_476 T_IsMonoidMonomorphism_404
                      (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_446 ::
  T_IsMonoidIsomorphism_438 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_446 v0
  = case coe v0 of
      C_constructor_476 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism.surjective
d_surjective_448 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_448 v0
  = case coe v0 of
      C_constructor_476 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.homo
d_homo_452 ::
  T_IsMonoidIsomorphism_438 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_452 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_412
            (coe d_isMonoidMonomorphism_446 (coe v0))))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.injective
d_injective_454 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_454 v0
  = coe d_injective_414 (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_456 ::
  T_IsMonoidIsomorphism_438 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_456 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_412
         (coe d_isMonoidMonomorphism_446 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_458 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_458 v7
du_isMagmaMonomorphism_458 ::
  T_IsMonoidIsomorphism_438 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_458 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_460 ::
  T_IsMonoidIsomorphism_438 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_460 v0
  = coe
      d_isMonoidHomomorphism_412
      (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_462 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_462 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_412
            (coe d_isMonoidMonomorphism_446 (coe v0))))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_464 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_464 v7
du_isRelMonomorphism_464 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_464 v0
  = let v1 = d_isMonoidMonomorphism_446 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v1)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.ε-homo
d_ε'45'homo_466 :: T_IsMonoidIsomorphism_438 -> AgdaAny
d_ε'45'homo_466 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_412
         (coe d_isMonoidMonomorphism_446 (coe v0)))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.cong
d_cong_468 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_468 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_412
               (coe d_isMonoidMonomorphism_446 (coe v0)))))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_470 v7
du_isMagmaIsomorphism_470 ::
  T_IsMonoidIsomorphism_438 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_470 v0
  = coe
      C_constructor_268
      (coe
         du_isMagmaMonomorphism_428
         (coe d_isMonoidMonomorphism_446 (coe v0)))
      (coe d_surjective_448 (coe v0))
-- Algebra.Morphism.Structures.MonoidMorphisms.IsMonoidIsomorphism._.isRelIsomorphism
d_isRelIsomorphism_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_474 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_474 v7
du_isRelIsomorphism_474 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_474 v0
  = coe
      du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._._⁻¹
d__'8315''185'_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  AgdaAny -> AgdaAny
d__'8315''185'_494 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8315''185'_494 v4
du__'8315''185'_494 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  AgdaAny -> AgdaAny
du__'8315''185'_494 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8315''185'_132 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._._≈_
d__'8776'__498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__498 = erased
-- Algebra.Morphism.Structures.GroupMorphisms._.Carrier
d_Carrier_502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 -> ()
d_Carrier_502 = erased
-- Algebra.Morphism.Structures.GroupMorphisms._.Homomorphic₁
d_Homomorphic'8321'_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_532 = erased
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaHomomorphism
d_IsMagmaHomomorphism_540 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism
d_IsMagmaIsomorphism_544 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism
d_IsMagmaMonomorphism_548 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaHomomorphism.homo
d_homo_554 ::
  T_IsMagmaHomomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_554 v0 = coe d_homo_204 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_556 ::
  T_IsMagmaHomomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_556 v0 = coe d_isRelHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaHomomorphism.cong
d_cong_558 ::
  T_IsMagmaHomomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_558 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.homo
d_homo_562 ::
  T_IsMagmaIsomorphism_240 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_562 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.injective
d_injective_564 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_564 v0
  = coe d_injective_224 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_566 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_566 v0
  = coe
      d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_568 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_568 v0
  = coe d_isMagmaMonomorphism_248 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_570 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_570 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_572
du_isRelIsomorphism_572 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_572 v0 v1 = coe du_isRelIsomorphism_266 v1
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_574 v7
du_isRelMonomorphism_574 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_574 v0
  = coe
      du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.surjective
d_surjective_576 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_576 v0 = coe d_surjective_250 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaIsomorphism.cong
d_cong_578 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_578 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_222
            (coe d_isMagmaMonomorphism_248 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.homo
d_homo_582 ::
  T_IsMagmaMonomorphism_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_582 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.injective
d_injective_584 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_584 v0 = coe d_injective_224 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_586 ::
  T_IsMagmaMonomorphism_214 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_586 v0
  = coe d_isMagmaHomomorphism_222 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_588 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_588 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_590 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_590
du_isRelMonomorphism_590 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_590 v0 v1 = coe du_isRelMonomorphism_234 v1
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMagmaMonomorphism.cong
d_cong_592 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_592 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism
d_IsMonoidHomomorphism_596 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism
d_IsMonoidIsomorphism_600 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism
d_IsMonoidMonomorphism_604 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism.homo
d_homo_610 ::
  T_IsMonoidHomomorphism_380 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_610 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_388 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_612 ::
  T_IsMonoidHomomorphism_380 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_612 v0
  = coe d_isMagmaHomomorphism_388 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism.isRelHomomorphism
d_isRelHomomorphism_614 ::
  T_IsMonoidHomomorphism_380 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_614 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_388 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism.ε-homo
d_ε'45'homo_616 :: T_IsMonoidHomomorphism_380 -> AgdaAny
d_ε'45'homo_616 v0 = coe d_ε'45'homo_390 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidHomomorphism.cong
d_cong_618 ::
  T_IsMonoidHomomorphism_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_618 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_388 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.homo
d_homo_622 ::
  T_IsMonoidIsomorphism_438 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_622 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_412
            (coe d_isMonoidMonomorphism_446 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.injective
d_injective_624 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_624 v0
  = coe d_injective_414 (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_626 ::
  T_IsMonoidIsomorphism_438 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_626 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_412
         (coe d_isMonoidMonomorphism_446 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_628 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaIsomorphism_628
du_isMagmaIsomorphism_628 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_628 v0 v1 = coe du_isMagmaIsomorphism_470 v1
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_630 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_630 v7
du_isMagmaMonomorphism_630 ::
  T_IsMonoidIsomorphism_438 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_630 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_632 ::
  T_IsMonoidIsomorphism_438 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_632 v0
  = coe
      d_isMonoidHomomorphism_412
      (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_634 ::
  T_IsMonoidIsomorphism_438 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_634 v0
  = coe d_isMonoidMonomorphism_446 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isRelHomomorphism
d_isRelHomomorphism_636 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_636 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_412
            (coe d_isMonoidMonomorphism_446 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isRelIsomorphism
d_isRelIsomorphism_638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_638 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_638 v7
du_isRelIsomorphism_638 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_638 v0
  = coe
      du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.isRelMonomorphism
d_isRelMonomorphism_640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_640 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_640 v7
du_isRelMonomorphism_640 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_640 v0
  = let v1 = d_isMonoidMonomorphism_446 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v1)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.surjective
d_surjective_642 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_642 v0 = coe d_surjective_448 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.ε-homo
d_ε'45'homo_644 :: T_IsMonoidIsomorphism_438 -> AgdaAny
d_ε'45'homo_644 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_412
         (coe d_isMonoidMonomorphism_446 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidIsomorphism.cong
d_cong_646 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_646 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_412
               (coe d_isMonoidMonomorphism_446 (coe v0)))))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.homo
d_homo_650 ::
  T_IsMonoidMonomorphism_404 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_650 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.injective
d_injective_652 ::
  T_IsMonoidMonomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_652 v0 = coe d_injective_414 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_654 ::
  T_IsMonoidMonomorphism_404 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_654 v0
  = coe
      d_isMagmaHomomorphism_388 (coe d_isMonoidHomomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaMonomorphism_656
du_isMagmaMonomorphism_656 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_656 v0 v1
  = coe du_isMagmaMonomorphism_428 v1
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_658 ::
  T_IsMonoidMonomorphism_404 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_658 v0
  = coe d_isMonoidHomomorphism_412 (coe v0)
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.isRelHomomorphism
d_isRelHomomorphism_660 ::
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_660 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.isRelMonomorphism
d_isRelMonomorphism_662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_662 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_662 v7
du_isRelMonomorphism_662 ::
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_662 v0
  = coe
      du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.ε-homo
d_ε'45'homo_664 :: T_IsMonoidMonomorphism_404 -> AgdaAny
d_ε'45'homo_664 v0
  = coe d_ε'45'homo_390 (coe d_isMonoidHomomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms._.IsMonoidMonomorphism.cong
d_cong_666 ::
  T_IsMonoidMonomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_666 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_isMonoidHomomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism
d_IsGroupHomomorphism_670 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsGroupHomomorphism_670
  = C_constructor_694 T_IsMonoidHomomorphism_380 (AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_678 ::
  T_IsGroupHomomorphism_670 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_678 v0
  = case coe v0 of
      C_constructor_694 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism.⁻¹-homo
d_'8315''185''45'homo_680 ::
  T_IsGroupHomomorphism_670 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_680 v0
  = case coe v0 of
      C_constructor_694 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism._.homo
d_homo_684 ::
  T_IsGroupHomomorphism_670 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_684 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_678 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_686 ::
  T_IsGroupHomomorphism_670 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_686 v0
  = coe
      d_isMagmaHomomorphism_388 (coe d_isMonoidHomomorphism_678 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_688 ::
  T_IsGroupHomomorphism_670 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_688 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_678 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism._.ε-homo
d_ε'45'homo_690 :: T_IsGroupHomomorphism_670 -> AgdaAny
d_ε'45'homo_690 v0
  = coe d_ε'45'homo_390 (coe d_isMonoidHomomorphism_678 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupHomomorphism._.cong
d_cong_692 ::
  T_IsGroupHomomorphism_670 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_692 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_isMonoidHomomorphism_678 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism
d_IsGroupMonomorphism_698 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsGroupMonomorphism_698
  = C_constructor_734 T_IsGroupHomomorphism_670
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism.isGroupHomomorphism
d_isGroupHomomorphism_706 ::
  T_IsGroupMonomorphism_698 -> T_IsGroupHomomorphism_670
d_isGroupHomomorphism_706 v0
  = case coe v0 of
      C_constructor_734 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism.injective
d_injective_708 ::
  T_IsGroupMonomorphism_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_708 v0
  = case coe v0 of
      C_constructor_734 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_712 ::
  T_IsGroupMonomorphism_698 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_712 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe d_isGroupHomomorphism_706 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_714 ::
  T_IsGroupMonomorphism_698 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_714 v0
  = coe
      d_isMonoidHomomorphism_678 (coe d_isGroupHomomorphism_706 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_716 ::
  T_IsGroupMonomorphism_698 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_716 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe d_isGroupHomomorphism_706 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.ε-homo
d_ε'45'homo_718 :: T_IsGroupMonomorphism_698 -> AgdaAny
d_ε'45'homo_718 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe d_isGroupHomomorphism_706 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.⁻¹-homo
d_'8315''185''45'homo_720 ::
  T_IsGroupMonomorphism_698 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_720 v0
  = coe
      d_'8315''185''45'homo_680 (coe d_isGroupHomomorphism_706 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.homo
d_homo_722 ::
  T_IsGroupMonomorphism_698 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_722 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe d_isGroupHomomorphism_706 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.cong
d_cong_724 ::
  T_IsGroupMonomorphism_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_724 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe d_isGroupHomomorphism_706 (coe v0)))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_698 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_726 v7
du_isMonoidMonomorphism_726 ::
  T_IsGroupMonomorphism_698 -> T_IsMonoidMonomorphism_404
du_isMonoidMonomorphism_726 v0
  = coe
      C_constructor_434
      (coe
         d_isMonoidHomomorphism_678
         (coe d_isGroupHomomorphism_706 (coe v0)))
      (coe d_injective_708 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_698 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_730 v7
du_isMagmaMonomorphism_730 ::
  T_IsGroupMonomorphism_698 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_730 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe du_isMonoidMonomorphism_726 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_698 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_732 v7
du_isRelMonomorphism_732 ::
  T_IsGroupMonomorphism_698 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_732 v0
  = let v1 = coe du_isMonoidMonomorphism_726 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v1)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism
d_IsGroupIsomorphism_738 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsGroupIsomorphism_738
  = C_constructor_784 T_IsGroupMonomorphism_698
                      (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism.isGroupMonomorphism
d_isGroupMonomorphism_746 ::
  T_IsGroupIsomorphism_738 -> T_IsGroupMonomorphism_698
d_isGroupMonomorphism_746 v0
  = case coe v0 of
      C_constructor_784 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism.surjective
d_surjective_748 ::
  T_IsGroupIsomorphism_738 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_748 v0
  = case coe v0 of
      C_constructor_784 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.injective
d_injective_752 ::
  T_IsGroupIsomorphism_738 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_752 v0
  = coe d_injective_708 (coe d_isGroupMonomorphism_746 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isGroupHomomorphism
d_isGroupHomomorphism_754 ::
  T_IsGroupIsomorphism_738 -> T_IsGroupHomomorphism_670
d_isGroupHomomorphism_754 v0
  = coe
      d_isGroupHomomorphism_706 (coe d_isGroupMonomorphism_746 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_756 ::
  T_IsGroupIsomorphism_738 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_756 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_isGroupHomomorphism_706
            (coe d_isGroupMonomorphism_746 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_758 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_758 v7
du_isMagmaMonomorphism_758 ::
  T_IsGroupIsomorphism_738 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_758 v0
  = let v1 = d_isGroupMonomorphism_746 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_428
         (coe du_isMonoidMonomorphism_726 (coe v1)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_760 ::
  T_IsGroupIsomorphism_738 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_760 v0
  = coe
      d_isMonoidHomomorphism_678
      (coe
         d_isGroupHomomorphism_706 (coe d_isGroupMonomorphism_746 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isMonoidMonomorphism
d_isMonoidMonomorphism_762 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_762 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_762 v7
du_isMonoidMonomorphism_762 ::
  T_IsGroupIsomorphism_738 -> T_IsMonoidMonomorphism_404
du_isMonoidMonomorphism_762 v0
  = coe
      du_isMonoidMonomorphism_726
      (coe d_isGroupMonomorphism_746 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_764 ::
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_764 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_isGroupHomomorphism_706
               (coe d_isGroupMonomorphism_746 (coe v0)))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_766 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_766 v7
du_isRelMonomorphism_766 ::
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_766 v0
  = let v1 = d_isGroupMonomorphism_746 (coe v0) in
    coe
      (let v2 = coe du_isMonoidMonomorphism_726 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_234
            (coe du_isMagmaMonomorphism_428 (coe v2))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.ε-homo
d_ε'45'homo_768 :: T_IsGroupIsomorphism_738 -> AgdaAny
d_ε'45'homo_768 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_isGroupHomomorphism_706
            (coe d_isGroupMonomorphism_746 (coe v0))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.⁻¹-homo
d_'8315''185''45'homo_770 ::
  T_IsGroupIsomorphism_738 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_770 v0
  = coe
      d_'8315''185''45'homo_680
      (coe
         d_isGroupHomomorphism_706 (coe d_isGroupMonomorphism_746 (coe v0)))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.homo
d_homo_772 ::
  T_IsGroupIsomorphism_738 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_772 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_isGroupHomomorphism_706
               (coe d_isGroupMonomorphism_746 (coe v0)))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.cong
d_cong_774 ::
  T_IsGroupIsomorphism_738 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_774 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe
                  d_isGroupHomomorphism_706
                  (coe d_isGroupMonomorphism_746 (coe v0))))))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism.isMonoidIsomorphism
d_isMonoidIsomorphism_776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMonoidIsomorphism_438
d_isMonoidIsomorphism_776 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidIsomorphism_776 v7
du_isMonoidIsomorphism_776 ::
  T_IsGroupIsomorphism_738 -> T_IsMonoidIsomorphism_438
du_isMonoidIsomorphism_776 v0
  = coe
      C_constructor_476
      (coe
         du_isMonoidMonomorphism_726
         (coe d_isGroupMonomorphism_746 (coe v0)))
      (coe d_surjective_748 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isMagmaIsomorphism
d_isMagmaIsomorphism_780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_780 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_780 v7
du_isMagmaIsomorphism_780 ::
  T_IsGroupIsomorphism_738 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_780 v0
  = coe
      du_isMagmaIsomorphism_470 (coe du_isMonoidIsomorphism_776 (coe v0))
-- Algebra.Morphism.Structures.GroupMorphisms.IsGroupIsomorphism._.isRelIsomorphism
d_isRelIsomorphism_782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_782 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_782 v7
du_isRelIsomorphism_782 ::
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_782 v0
  = let v1 = coe du_isMonoidIsomorphism_776 (coe v0) in
    coe
      (coe
         du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms._._*_
d__'42'__802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'42'__802 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'42'__802 v4
du__'42'__802 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'42'__802 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__170 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms._._≈_
d__'8776'__806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__806 = erased
-- Algebra.Morphism.Structures.NearSemiringMorphisms._.Carrier
d_Carrier_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 -> ()
d_Carrier_818 = erased
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism
d_IsMonoidHomomorphism_842 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism
d_IsMonoidIsomorphism_846 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism
d_IsMonoidMonomorphism_850 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism.homo
d_homo_856 ::
  T_IsMonoidHomomorphism_380 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_856 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_388 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_858 ::
  T_IsMonoidHomomorphism_380 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_858 v0
  = coe d_isMagmaHomomorphism_388 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism.isRelHomomorphism
d_isRelHomomorphism_860 ::
  T_IsMonoidHomomorphism_380 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_860 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_388 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism.ε-homo
d_ε'45'homo_862 :: T_IsMonoidHomomorphism_380 -> AgdaAny
d_ε'45'homo_862 v0 = coe d_ε'45'homo_390 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidHomomorphism.cong
d_cong_864 ::
  T_IsMonoidHomomorphism_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_864 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_388 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.homo
d_homo_868 ::
  T_IsMonoidIsomorphism_438 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_868 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_412
            (coe d_isMonoidMonomorphism_446 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.injective
d_injective_870 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_870 v0
  = coe d_injective_414 (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_872 ::
  T_IsMonoidIsomorphism_438 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_872 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_412
         (coe d_isMonoidMonomorphism_446 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_874 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaIsomorphism_874
du_isMagmaIsomorphism_874 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_874 v0 v1 = coe du_isMagmaIsomorphism_470 v1
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_876 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_876 v7
du_isMagmaMonomorphism_876 ::
  T_IsMonoidIsomorphism_438 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_876 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_878 ::
  T_IsMonoidIsomorphism_438 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_878 v0
  = coe
      d_isMonoidHomomorphism_412
      (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_880 ::
  T_IsMonoidIsomorphism_438 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_880 v0
  = coe d_isMonoidMonomorphism_446 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isRelHomomorphism
d_isRelHomomorphism_882 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_882 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_412
            (coe d_isMonoidMonomorphism_446 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isRelIsomorphism
d_isRelIsomorphism_884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_884 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_884 v7
du_isRelIsomorphism_884 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_884 v0
  = coe
      du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.isRelMonomorphism
d_isRelMonomorphism_886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_886 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_886 v7
du_isRelMonomorphism_886 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_886 v0
  = let v1 = d_isMonoidMonomorphism_446 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.surjective
d_surjective_888 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_888 v0 = coe d_surjective_448 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.ε-homo
d_ε'45'homo_890 :: T_IsMonoidIsomorphism_438 -> AgdaAny
d_ε'45'homo_890 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_412
         (coe d_isMonoidMonomorphism_446 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidIsomorphism.cong
d_cong_892 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_892 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_412
               (coe d_isMonoidMonomorphism_446 (coe v0)))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.homo
d_homo_896 ::
  T_IsMonoidMonomorphism_404 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_896 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.injective
d_injective_898 ::
  T_IsMonoidMonomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_898 v0 = coe d_injective_414 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_900 ::
  T_IsMonoidMonomorphism_404 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_900 v0
  = coe
      d_isMagmaHomomorphism_388 (coe d_isMonoidHomomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_902 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_902 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaMonomorphism_902
du_isMagmaMonomorphism_902 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_902 v0 v1
  = coe du_isMagmaMonomorphism_428 v1
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_904 ::
  T_IsMonoidMonomorphism_404 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_904 v0
  = coe d_isMonoidHomomorphism_412 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.isRelHomomorphism
d_isRelHomomorphism_906 ::
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_906 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.isRelMonomorphism
d_isRelMonomorphism_908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_908 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_908 v7
du_isRelMonomorphism_908 ::
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_908 v0
  = coe
      du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.ε-homo
d_ε'45'homo_910 :: T_IsMonoidMonomorphism_404 -> AgdaAny
d_ε'45'homo_910 v0
  = coe d_ε'45'homo_390 (coe d_isMonoidHomomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.+.IsMonoidMonomorphism.cong
d_cong_912 ::
  T_IsMonoidMonomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_912 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_isMonoidHomomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaHomomorphism
d_IsMagmaHomomorphism_916 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism
d_IsMagmaIsomorphism_920 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism
d_IsMagmaMonomorphism_924 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaHomomorphism.homo
d_homo_930 ::
  T_IsMagmaHomomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_930 v0 = coe d_homo_204 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_932 ::
  T_IsMagmaHomomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_932 v0 = coe d_isRelHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaHomomorphism.cong
d_cong_934 ::
  T_IsMagmaHomomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_934 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.homo
d_homo_938 ::
  T_IsMagmaIsomorphism_240 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_938 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.injective
d_injective_940 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_940 v0
  = coe d_injective_224 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_942 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_942 v0
  = coe
      d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_944 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_944 v0
  = coe d_isMagmaMonomorphism_248 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_946 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_946 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_948
du_isRelIsomorphism_948 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_948 v0 v1 = coe du_isRelIsomorphism_266 v1
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_950 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_950 v7
du_isRelMonomorphism_950 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_950 v0
  = coe
      du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.surjective
d_surjective_952 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_952 v0 = coe d_surjective_250 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaIsomorphism.cong
d_cong_954 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_954 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_222
            (coe d_isMagmaMonomorphism_248 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.homo
d_homo_958 ::
  T_IsMagmaMonomorphism_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_958 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.injective
d_injective_960 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_960 v0 = coe d_injective_224 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_962 ::
  T_IsMagmaMonomorphism_214 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_962 v0
  = coe d_isMagmaHomomorphism_222 (coe v0)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_964 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_964 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_966 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_966
du_isRelMonomorphism_966 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_966 v0 v1 = coe du_isRelMonomorphism_234 v1
-- Algebra.Morphism.Structures.NearSemiringMorphisms.*.IsMagmaMonomorphism.cong
d_cong_968 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_968 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms._.Homomorphic₂
d_Homomorphic'8322'_976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_976 = erased
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism
d_IsNearSemiringHomomorphism_982 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsNearSemiringHomomorphism_982
  = C_constructor_1008 T_IsMonoidHomomorphism_380
                       (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_990 ::
  T_IsNearSemiringHomomorphism_982 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_990 v0
  = case coe v0 of
      C_constructor_1008 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism.*-homo
d_'42''45'homo_992 ::
  T_IsNearSemiringHomomorphism_982 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_992 v0
  = case coe v0 of
      C_constructor_1008 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism._.homo
d_homo_996 ::
  T_IsNearSemiringHomomorphism_982 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_996 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe d_'43''45'isMonoidHomomorphism_990 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_998 ::
  T_IsNearSemiringHomomorphism_982 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_998 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe d_'43''45'isMonoidHomomorphism_990 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism._.ε-homo
d_ε'45'homo_1000 :: T_IsNearSemiringHomomorphism_982 -> AgdaAny
d_ε'45'homo_1000 v0
  = coe
      d_ε'45'homo_390 (coe d_'43''45'isMonoidHomomorphism_990 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_1002 ::
  T_IsNearSemiringHomomorphism_982 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1002 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe d_'43''45'isMonoidHomomorphism_990 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism._.cong
d_cong_1004 ::
  T_IsNearSemiringHomomorphism_982 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1004 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_'43''45'isMonoidHomomorphism_990 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringHomomorphism_982 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1006 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1006 v7
du_'42''45'isMagmaHomomorphism_1006 ::
  T_IsNearSemiringHomomorphism_982 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1006 v0
  = coe
      C_constructor_210
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_'43''45'isMonoidHomomorphism_990 (coe v0))))
      (coe d_'42''45'homo_992 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism
d_IsNearSemiringMonomorphism_1012 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsNearSemiringMonomorphism_1012
  = C_constructor_1052 T_IsNearSemiringHomomorphism_982
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1020 ::
  T_IsNearSemiringMonomorphism_1012 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1020 v0
  = case coe v0 of
      C_constructor_1052 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism.injective
d_injective_1022 ::
  T_IsNearSemiringMonomorphism_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1022 v0
  = case coe v0 of
      C_constructor_1052 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.*-homo
d_'42''45'homo_1026 ::
  T_IsNearSemiringMonomorphism_1012 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1026 v0
  = coe
      d_'42''45'homo_992 (coe d_isNearSemiringHomomorphism_1020 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1028 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1028 v7
du_'42''45'isMagmaHomomorphism_1028 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1028 v0
  = coe
      du_'42''45'isMagmaHomomorphism_1006
      (coe d_isNearSemiringHomomorphism_1020 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.homo
d_homo_1030 ::
  T_IsNearSemiringMonomorphism_1012 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1030 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1020 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1032 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1032 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1020 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1034 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_1034 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe d_isNearSemiringHomomorphism_1020 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.ε-homo
d_ε'45'homo_1036 :: T_IsNearSemiringMonomorphism_1012 -> AgdaAny
d_ε'45'homo_1036 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1020 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_1038 ::
  T_IsNearSemiringMonomorphism_1012 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1038 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1020 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.cong
d_cong_1040 ::
  T_IsNearSemiringMonomorphism_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1040 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe d_isNearSemiringHomomorphism_1020 (coe v0)))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1042 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_1042 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_1042 v7
du_'43''45'isMonoidMonomorphism_1042 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_1042 v0
  = coe
      C_constructor_434
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1020 (coe v0)))
      (coe d_injective_1022 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_1046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1046 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1046 v7
du_isMagmaMonomorphism_1046 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1046 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe du_'43''45'isMonoidMonomorphism_1042 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_1048 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1048 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1048 v7
du_isRelMonomorphism_1048 ::
  T_IsNearSemiringMonomorphism_1012 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1048 v0
  = let v1 = coe du_'43''45'isMonoidMonomorphism_1042 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_1050 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1050 v7
du_'42''45'isMagmaMonomorphism_1050 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_1050 v0
  = coe
      C_constructor_236
      (coe
         du_'42''45'isMagmaHomomorphism_1006
         (coe d_isNearSemiringHomomorphism_1020 (coe v0)))
      (coe d_injective_1022 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism
d_IsNearSemiringIsomorphism_1056 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsNearSemiringIsomorphism_1056
  = C_constructor_1108 T_IsNearSemiringMonomorphism_1012
                       (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_1064 ::
  T_IsNearSemiringIsomorphism_1056 ->
  T_IsNearSemiringMonomorphism_1012
d_isNearSemiringMonomorphism_1064 v0
  = case coe v0 of
      C_constructor_1108 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism.surjective
d_surjective_1066 ::
  T_IsNearSemiringIsomorphism_1056 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1066 v0
  = case coe v0 of
      C_constructor_1108 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.*-homo
d_'42''45'homo_1070 ::
  T_IsNearSemiringIsomorphism_1056 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1070 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1020
         (coe d_isNearSemiringMonomorphism_1064 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1072 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1072 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1072 v7
du_'42''45'isMagmaHomomorphism_1072 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1072 v0
  = let v1 = d_isNearSemiringMonomorphism_1064 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_1006
         (coe d_isNearSemiringHomomorphism_1020 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_1074 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1074 v7
du_'42''45'isMagmaMonomorphism_1074 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_1074 v0
  = coe
      du_'42''45'isMagmaMonomorphism_1050
      (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.homo
d_homo_1076 ::
  T_IsNearSemiringIsomorphism_1056 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1076 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1020
               (coe d_isNearSemiringMonomorphism_1064 (coe v0)))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1078 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1078 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1020
            (coe d_isNearSemiringMonomorphism_1064 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_1080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1080 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1080 v7
du_isMagmaMonomorphism_1080 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1080 v0
  = let v1 = d_isNearSemiringMonomorphism_1064 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_428
         (coe du_'43''45'isMonoidMonomorphism_1042 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1082 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_1082 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1020
         (coe d_isNearSemiringMonomorphism_1064 (coe v0)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1084 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_1084 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_1084 v7
du_'43''45'isMonoidMonomorphism_1084 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_1084 v0
  = coe
      du_'43''45'isMonoidMonomorphism_1042
      (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.ε-homo
d_ε'45'homo_1086 :: T_IsNearSemiringIsomorphism_1056 -> AgdaAny
d_ε'45'homo_1086 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1020
            (coe d_isNearSemiringMonomorphism_1064 (coe v0))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.injective
d_injective_1088 ::
  T_IsNearSemiringIsomorphism_1056 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1088 v0
  = coe
      d_injective_1022 (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1090 ::
  T_IsNearSemiringIsomorphism_1056 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1090 v0
  = coe
      d_isNearSemiringHomomorphism_1020
      (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_1092 ::
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1092 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1020
               (coe d_isNearSemiringMonomorphism_1064 (coe v0)))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_1094 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1094 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1094 v7
du_isRelMonomorphism_1094 ::
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1094 v0
  = let v1 = d_isNearSemiringMonomorphism_1064 (coe v0) in
    coe
      (let v2 = coe du_'43''45'isMonoidMonomorphism_1042 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_234
            (coe du_isMagmaMonomorphism_428 (coe v2))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.cong
d_cong_1096 ::
  T_IsNearSemiringIsomorphism_1056 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1096 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1020
                  (coe d_isNearSemiringMonomorphism_1064 (coe v0))))))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism.+-isMonoidIsomorphism
d_'43''45'isMonoidIsomorphism_1098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidIsomorphism_438
d_'43''45'isMonoidIsomorphism_1098 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidIsomorphism_1098 v7
du_'43''45'isMonoidIsomorphism_1098 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidIsomorphism_438
du_'43''45'isMonoidIsomorphism_1098 v0
  = coe
      C_constructor_476
      (coe
         du_'43''45'isMonoidMonomorphism_1042
         (coe d_isNearSemiringMonomorphism_1064 (coe v0)))
      (coe d_surjective_1066 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isMagmaIsomorphism
d_isMagmaIsomorphism_1102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_1102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_1102 v7
du_isMagmaIsomorphism_1102 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_1102 v0
  = coe
      du_isMagmaIsomorphism_470
      (coe du_'43''45'isMonoidIsomorphism_1098 (coe v0))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism._.isRelIsomorphism
d_isRelIsomorphism_1104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_1104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1104 v7
du_isRelIsomorphism_1104 ::
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_1104 v0
  = let v1 = coe du_'43''45'isMonoidIsomorphism_1098 (coe v0) in
    coe
      (coe
         du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v1)))
-- Algebra.Morphism.Structures.NearSemiringMorphisms.IsNearSemiringIsomorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_1106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
d_'42''45'isMagmaIsomorphism_1106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaIsomorphism_1106 v7
du_'42''45'isMagmaIsomorphism_1106 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
du_'42''45'isMagmaIsomorphism_1106 v0
  = coe
      C_constructor_268
      (coe
         du_'42''45'isMagmaMonomorphism_1050
         (coe d_isNearSemiringMonomorphism_1064 (coe v0)))
      (coe d_surjective_1066 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._._≈_
d__'8776'__1130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1130 = erased
-- Algebra.Morphism.Structures.SemiringMorphisms._.1#
d_1'35'_1144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 -> AgdaAny
d_1'35'_1144 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_1'35'_1144 v4
du_1'35'_1144 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 -> AgdaAny
du_1'35'_1144 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_1'35'_218 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.Carrier
d_Carrier_1146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 -> ()
d_Carrier_1146 = erased
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism
d_IsMonoidHomomorphism_1178 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism
d_IsMonoidIsomorphism_1182 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism
d_IsMonoidMonomorphism_1186 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism.homo
d_homo_1192 ::
  T_IsMonoidHomomorphism_380 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1192 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_388 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1194 ::
  T_IsMonoidHomomorphism_380 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1194 v0
  = coe d_isMagmaHomomorphism_388 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism.isRelHomomorphism
d_isRelHomomorphism_1196 ::
  T_IsMonoidHomomorphism_380 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1196 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_388 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism.ε-homo
d_ε'45'homo_1198 :: T_IsMonoidHomomorphism_380 -> AgdaAny
d_ε'45'homo_1198 v0 = coe d_ε'45'homo_390 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidHomomorphism.cong
d_cong_1200 ::
  T_IsMonoidHomomorphism_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1200 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_388 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.homo
d_homo_1204 ::
  T_IsMonoidIsomorphism_438 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1204 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_412
            (coe d_isMonoidMonomorphism_446 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.injective
d_injective_1206 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1206 v0
  = coe d_injective_414 (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1208 ::
  T_IsMonoidIsomorphism_438 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1208 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_412
         (coe d_isMonoidMonomorphism_446 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_1210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_1210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaIsomorphism_1210
du_isMagmaIsomorphism_1210 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_1210 v0 v1 = coe du_isMagmaIsomorphism_470 v1
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1212 v7
du_isMagmaMonomorphism_1212 ::
  T_IsMonoidIsomorphism_438 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1212 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1214 ::
  T_IsMonoidIsomorphism_438 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_1214 v0
  = coe
      d_isMonoidHomomorphism_412
      (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_1216 ::
  T_IsMonoidIsomorphism_438 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_1216 v0
  = coe d_isMonoidMonomorphism_446 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isRelHomomorphism
d_isRelHomomorphism_1218 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1218 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_412
            (coe d_isMonoidMonomorphism_446 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isRelIsomorphism
d_isRelIsomorphism_1220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_1220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1220 v7
du_isRelIsomorphism_1220 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_1220 v0
  = coe
      du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.isRelMonomorphism
d_isRelMonomorphism_1222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1222 v7
du_isRelMonomorphism_1222 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1222 v0
  = let v1 = d_isMonoidMonomorphism_446 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.surjective
d_surjective_1224 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1224 v0 = coe d_surjective_448 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.ε-homo
d_ε'45'homo_1226 :: T_IsMonoidIsomorphism_438 -> AgdaAny
d_ε'45'homo_1226 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_412
         (coe d_isMonoidMonomorphism_446 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidIsomorphism.cong
d_cong_1228 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1228 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_412
               (coe d_isMonoidMonomorphism_446 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.homo
d_homo_1232 ::
  T_IsMonoidMonomorphism_404 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1232 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.injective
d_injective_1234 ::
  T_IsMonoidMonomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1234 v0 = coe d_injective_414 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1236 ::
  T_IsMonoidMonomorphism_404 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1236 v0
  = coe
      d_isMagmaHomomorphism_388 (coe d_isMonoidHomomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1238 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaMonomorphism_1238
du_isMagmaMonomorphism_1238 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1238 v0 v1
  = coe du_isMagmaMonomorphism_428 v1
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1240 ::
  T_IsMonoidMonomorphism_404 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_1240 v0
  = coe d_isMonoidHomomorphism_412 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.isRelHomomorphism
d_isRelHomomorphism_1242 ::
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1242 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.isRelMonomorphism
d_isRelMonomorphism_1244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1244 v7
du_isRelMonomorphism_1244 ::
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1244 v0
  = coe
      du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.ε-homo
d_ε'45'homo_1246 :: T_IsMonoidMonomorphism_404 -> AgdaAny
d_ε'45'homo_1246 v0
  = coe d_ε'45'homo_390 (coe d_isMonoidHomomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.*.IsMonoidMonomorphism.cong
d_cong_1248 ::
  T_IsMonoidMonomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1248 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_isMonoidHomomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.Homomorphic₀
d_Homomorphic'8320'_1252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_1252 = erased
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism
d_IsNearSemiringHomomorphism_1262 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism
d_IsNearSemiringIsomorphism_1266 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism
d_IsNearSemiringMonomorphism_1270 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.*-homo
d_'42''45'homo_1276 ::
  T_IsNearSemiringHomomorphism_982 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1276 v0 = coe d_'42''45'homo_992 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringHomomorphism_982 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaHomomorphism_1278
du_'42''45'isMagmaHomomorphism_1278 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringHomomorphism_982 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1278 v0 v1
  = coe du_'42''45'isMagmaHomomorphism_1006 v1
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.homo
d_homo_1280 ::
  T_IsNearSemiringHomomorphism_982 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1280 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe d_'43''45'isMonoidHomomorphism_990 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1282 ::
  T_IsNearSemiringHomomorphism_982 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1282 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe d_'43''45'isMonoidHomomorphism_990 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1284 ::
  T_IsNearSemiringHomomorphism_982 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_1284 v0
  = coe d_'43''45'isMonoidHomomorphism_990 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.ε-homo
d_ε'45'homo_1286 :: T_IsNearSemiringHomomorphism_982 -> AgdaAny
d_ε'45'homo_1286 v0
  = coe
      d_ε'45'homo_390 (coe d_'43''45'isMonoidHomomorphism_990 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.isRelHomomorphism
d_isRelHomomorphism_1288 ::
  T_IsNearSemiringHomomorphism_982 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1288 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe d_'43''45'isMonoidHomomorphism_990 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringHomomorphism.cong
d_cong_1290 ::
  T_IsNearSemiringHomomorphism_982 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1290 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_'43''45'isMonoidHomomorphism_990 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.*-homo
d_'42''45'homo_1294 ::
  T_IsNearSemiringIsomorphism_1056 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1294 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1020
         (coe d_isNearSemiringMonomorphism_1064 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1296 v7
du_'42''45'isMagmaHomomorphism_1296 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1296 v0
  = let v1 = d_isNearSemiringMonomorphism_1064 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_1006
         (coe d_isNearSemiringHomomorphism_1020 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_1298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
d_'42''45'isMagmaIsomorphism_1298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaIsomorphism_1298
du_'42''45'isMagmaIsomorphism_1298 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
du_'42''45'isMagmaIsomorphism_1298 v0 v1
  = coe du_'42''45'isMagmaIsomorphism_1106 v1
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_1300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1300 v7
du_'42''45'isMagmaMonomorphism_1300 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_1300 v0
  = coe
      du_'42''45'isMagmaMonomorphism_1050
      (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.homo
d_homo_1302 ::
  T_IsNearSemiringIsomorphism_1056 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1302 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1020
               (coe d_isNearSemiringMonomorphism_1064 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1304 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1304 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1020
            (coe d_isNearSemiringMonomorphism_1064 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_1306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_1306 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_1306 v7
du_isMagmaIsomorphism_1306 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_1306 v0
  = coe
      du_isMagmaIsomorphism_470
      (coe du_'43''45'isMonoidIsomorphism_1098 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1308 v7
du_isMagmaMonomorphism_1308 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1308 v0
  = let v1 = d_isNearSemiringMonomorphism_1064 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_428
         (coe du_'43''45'isMonoidMonomorphism_1042 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1310 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_1310 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1020
         (coe d_isNearSemiringMonomorphism_1064 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.+-isMonoidIsomorphism
d_'43''45'isMonoidIsomorphism_1312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidIsomorphism_438
d_'43''45'isMonoidIsomorphism_1312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'43''45'isMonoidIsomorphism_1312
du_'43''45'isMonoidIsomorphism_1312 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidIsomorphism_438
du_'43''45'isMonoidIsomorphism_1312 v0 v1
  = coe du_'43''45'isMonoidIsomorphism_1098 v1
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_1314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_1314 v7
du_'43''45'isMonoidMonomorphism_1314 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_1314 v0
  = coe
      du_'43''45'isMonoidMonomorphism_1042
      (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.ε-homo
d_ε'45'homo_1316 :: T_IsNearSemiringIsomorphism_1056 -> AgdaAny
d_ε'45'homo_1316 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1020
            (coe d_isNearSemiringMonomorphism_1064 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.injective
d_injective_1318 ::
  T_IsNearSemiringIsomorphism_1056 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1318 v0
  = coe
      d_injective_1022 (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1320 ::
  T_IsNearSemiringIsomorphism_1056 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1320 v0
  = coe
      d_isNearSemiringHomomorphism_1020
      (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_1322 ::
  T_IsNearSemiringIsomorphism_1056 ->
  T_IsNearSemiringMonomorphism_1012
d_isNearSemiringMonomorphism_1322 v0
  = coe d_isNearSemiringMonomorphism_1064 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isRelHomomorphism
d_isRelHomomorphism_1324 ::
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1324 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1020
               (coe d_isNearSemiringMonomorphism_1064 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isRelIsomorphism
d_isRelIsomorphism_1326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_1326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1326 v7
du_isRelIsomorphism_1326 ::
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_1326 v0
  = let v1 = coe du_'43''45'isMonoidIsomorphism_1098 (coe v0) in
    coe
      (coe
         du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.isRelMonomorphism
d_isRelMonomorphism_1328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1328 v7
du_isRelMonomorphism_1328 ::
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1328 v0
  = let v1 = d_isNearSemiringMonomorphism_1064 (coe v0) in
    coe
      (let v2 = coe du_'43''45'isMonoidMonomorphism_1042 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_234
            (coe du_isMagmaMonomorphism_428 (coe v2))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.surjective
d_surjective_1330 ::
  T_IsNearSemiringIsomorphism_1056 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1330 v0 = coe d_surjective_1066 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringIsomorphism.cong
d_cong_1332 ::
  T_IsNearSemiringIsomorphism_1056 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1332 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1020
                  (coe d_isNearSemiringMonomorphism_1064 (coe v0))))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.*-homo
d_'42''45'homo_1336 ::
  T_IsNearSemiringMonomorphism_1012 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1336 v0
  = coe
      d_'42''45'homo_992 (coe d_isNearSemiringHomomorphism_1020 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1338 v7
du_'42''45'isMagmaHomomorphism_1338 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1338 v0
  = coe
      du_'42''45'isMagmaHomomorphism_1006
      (coe d_isNearSemiringHomomorphism_1020 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_1340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaMonomorphism_1340
du_'42''45'isMagmaMonomorphism_1340 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_1340 v0 v1
  = coe du_'42''45'isMagmaMonomorphism_1050 v1
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.homo
d_homo_1342 ::
  T_IsNearSemiringMonomorphism_1012 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1342 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1020 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1344 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1344 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1020 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1346 v7
du_isMagmaMonomorphism_1346 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1346 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe du_'43''45'isMonoidMonomorphism_1042 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1348 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_1348 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe d_isNearSemiringHomomorphism_1020 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_1350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'43''45'isMonoidMonomorphism_1350
du_'43''45'isMonoidMonomorphism_1350 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_1350 v0 v1
  = coe du_'43''45'isMonoidMonomorphism_1042 v1
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.ε-homo
d_ε'45'homo_1352 :: T_IsNearSemiringMonomorphism_1012 -> AgdaAny
d_ε'45'homo_1352 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1020 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.injective
d_injective_1354 ::
  T_IsNearSemiringMonomorphism_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1354 v0 = coe d_injective_1022 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1356 ::
  T_IsNearSemiringMonomorphism_1012 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1356 v0
  = coe d_isNearSemiringHomomorphism_1020 (coe v0)
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.isRelHomomorphism
d_isRelHomomorphism_1358 ::
  T_IsNearSemiringMonomorphism_1012 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1358 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1020 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.isRelMonomorphism
d_isRelMonomorphism_1360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1360 v7
du_isRelMonomorphism_1360 ::
  T_IsNearSemiringMonomorphism_1012 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1360 v0
  = let v1 = coe du_'43''45'isMonoidMonomorphism_1042 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms._.IsNearSemiringMonomorphism.cong
d_cong_1362 ::
  T_IsNearSemiringMonomorphism_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1362 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe d_isNearSemiringHomomorphism_1020 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism
d_IsSemiringHomomorphism_1366 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemiringHomomorphism_1366
  = C_constructor_1398 T_IsNearSemiringHomomorphism_982 AgdaAny
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1374 ::
  T_IsSemiringHomomorphism_1366 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1374 v0
  = case coe v0 of
      C_constructor_1398 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism.1#-homo
d_1'35''45'homo_1376 :: T_IsSemiringHomomorphism_1366 -> AgdaAny
d_1'35''45'homo_1376 v0
  = case coe v0 of
      C_constructor_1398 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.*-homo
d_'42''45'homo_1380 ::
  T_IsSemiringHomomorphism_1366 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1380 v0
  = coe
      d_'42''45'homo_992 (coe d_isNearSemiringHomomorphism_1374 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1366 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1382 v7
du_'42''45'isMagmaHomomorphism_1382 ::
  T_IsSemiringHomomorphism_1366 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1382 v0
  = coe
      du_'42''45'isMagmaHomomorphism_1006
      (coe d_isNearSemiringHomomorphism_1374 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.homo
d_homo_1384 ::
  T_IsSemiringHomomorphism_1366 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1384 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1374 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1386 ::
  T_IsSemiringHomomorphism_1366 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1386 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1374 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1388 ::
  T_IsSemiringHomomorphism_1366 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_1388 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe d_isNearSemiringHomomorphism_1374 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.ε-homo
d_ε'45'homo_1390 :: T_IsSemiringHomomorphism_1366 -> AgdaAny
d_ε'45'homo_1390 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1374 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_1392 ::
  T_IsSemiringHomomorphism_1366 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1392 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1374 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism._.cong
d_cong_1394 ::
  T_IsSemiringHomomorphism_1366 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1394 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe d_isNearSemiringHomomorphism_1374 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringHomomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_1396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1366 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_1396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_1396 v7
du_'42''45'isMonoidHomomorphism_1396 ::
  T_IsSemiringHomomorphism_1366 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_1396 v0
  = coe
      C_constructor_400
      (coe
         du_'42''45'isMagmaHomomorphism_1006
         (coe d_isNearSemiringHomomorphism_1374 (coe v0)))
      (coe d_1'35''45'homo_1376 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism
d_IsSemiringMonomorphism_1402 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemiringMonomorphism_1402
  = C_constructor_1448 T_IsSemiringHomomorphism_1366
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_1410 ::
  T_IsSemiringMonomorphism_1402 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_1410 v0
  = case coe v0 of
      C_constructor_1448 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism.injective
d_injective_1412 ::
  T_IsSemiringMonomorphism_1402 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1412 v0
  = case coe v0 of
      C_constructor_1448 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.*-homo
d_'42''45'homo_1416 ::
  T_IsSemiringMonomorphism_1402 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1416 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe d_isSemiringHomomorphism_1410 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1418 v7
du_'42''45'isMagmaHomomorphism_1418 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1418 v0
  = let v1 = d_isSemiringHomomorphism_1410 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_1006
         (coe d_isNearSemiringHomomorphism_1374 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_1420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_1420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_1420 v7
du_'42''45'isMonoidHomomorphism_1420 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_1420 v0
  = coe
      du_'42''45'isMonoidHomomorphism_1396
      (coe d_isSemiringHomomorphism_1410 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.homo
d_homo_1422 ::
  T_IsSemiringMonomorphism_1402 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1422 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe d_isSemiringHomomorphism_1410 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1424 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1424 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_1410 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1426 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_1426 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe d_isSemiringHomomorphism_1410 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.ε-homo
d_ε'45'homo_1428 :: T_IsSemiringMonomorphism_1402 -> AgdaAny
d_ε'45'homo_1428 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_1410 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.1#-homo
d_1'35''45'homo_1430 :: T_IsSemiringMonomorphism_1402 -> AgdaAny
d_1'35''45'homo_1430 v0
  = coe
      d_1'35''45'homo_1376 (coe d_isSemiringHomomorphism_1410 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1432 ::
  T_IsSemiringMonomorphism_1402 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1432 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe d_isSemiringHomomorphism_1410 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_1434 ::
  T_IsSemiringMonomorphism_1402 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1434 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe d_isSemiringHomomorphism_1410 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.cong
d_cong_1436 ::
  T_IsSemiringMonomorphism_1402 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1436 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe d_isSemiringHomomorphism_1410 (coe v0))))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_1438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsNearSemiringMonomorphism_1012
d_isNearSemiringMonomorphism_1438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringMonomorphism_1438 v7
du_isNearSemiringMonomorphism_1438 ::
  T_IsSemiringMonomorphism_1402 -> T_IsNearSemiringMonomorphism_1012
du_isNearSemiringMonomorphism_1438 v0
  = coe
      C_constructor_1052
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe d_isSemiringHomomorphism_1410 (coe v0)))
      (coe d_injective_1412 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_1442 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1442 v7
du_'42''45'isMagmaMonomorphism_1442 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_1442 v0
  = coe
      du_'42''45'isMagmaMonomorphism_1050
      (coe du_isNearSemiringMonomorphism_1438 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism._.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_1444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_1444 v7
du_'43''45'isMonoidMonomorphism_1444 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_1444 v0
  = coe
      du_'43''45'isMonoidMonomorphism_1042
      (coe du_isNearSemiringMonomorphism_1438 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringMonomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_1446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
d_'42''45'isMonoidMonomorphism_1446 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_1446 v7
du_'42''45'isMonoidMonomorphism_1446 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
du_'42''45'isMonoidMonomorphism_1446 v0
  = coe
      C_constructor_434
      (coe
         du_'42''45'isMonoidHomomorphism_1396
         (coe d_isSemiringHomomorphism_1410 (coe v0)))
      (coe d_injective_1412 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism
d_IsSemiringIsomorphism_1452 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemiringIsomorphism_1452
  = C_constructor_1510 T_IsSemiringMonomorphism_1402
                       (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism.isSemiringMonomorphism
d_isSemiringMonomorphism_1460 ::
  T_IsSemiringIsomorphism_1452 -> T_IsSemiringMonomorphism_1402
d_isSemiringMonomorphism_1460 v0
  = case coe v0 of
      C_constructor_1510 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism.surjective
d_surjective_1462 ::
  T_IsSemiringIsomorphism_1452 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1462 v0
  = case coe v0 of
      C_constructor_1510 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-homo
d_'42''45'homo_1466 ::
  T_IsSemiringIsomorphism_1452 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1466 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_1410
            (coe d_isSemiringMonomorphism_1460 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1468 v7
du_'42''45'isMagmaHomomorphism_1468 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1468 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (let v2 = d_isSemiringHomomorphism_1410 (coe v1) in
       coe
         (coe
            du_'42''45'isMagmaHomomorphism_1006
            (coe d_isNearSemiringHomomorphism_1374 (coe v2))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_1470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1470 v7
du_'42''45'isMagmaMonomorphism_1470 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_1470 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaMonomorphism_1050
         (coe du_isNearSemiringMonomorphism_1438 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_1472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_1472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_1472 v7
du_'42''45'isMonoidHomomorphism_1472 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_1472 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoidHomomorphism_1396
         (coe d_isSemiringHomomorphism_1410 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_1474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
d_'42''45'isMonoidMonomorphism_1474 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_1474 v7
du_'42''45'isMonoidMonomorphism_1474 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
du_'42''45'isMonoidMonomorphism_1474 v0
  = coe
      du_'42''45'isMonoidMonomorphism_1446
      (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.homo
d_homo_1476 ::
  T_IsSemiringIsomorphism_1452 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1476 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_1410
                  (coe d_isSemiringMonomorphism_1460 (coe v0))))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1478 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1478 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_1410
               (coe d_isSemiringMonomorphism_1460 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1480 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_1480 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_1410
            (coe d_isSemiringMonomorphism_1460 (coe v0))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_1482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_1482 v7
du_'43''45'isMonoidMonomorphism_1482 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_1482 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (coe
         du_'43''45'isMonoidMonomorphism_1042
         (coe du_isNearSemiringMonomorphism_1438 (coe v1)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.ε-homo
d_ε'45'homo_1484 :: T_IsSemiringIsomorphism_1452 -> AgdaAny
d_ε'45'homo_1484 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_1410
               (coe d_isSemiringMonomorphism_1460 (coe v0)))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.1#-homo
d_1'35''45'homo_1486 :: T_IsSemiringIsomorphism_1452 -> AgdaAny
d_1'35''45'homo_1486 v0
  = coe
      d_1'35''45'homo_1376
      (coe
         d_isSemiringHomomorphism_1410
         (coe d_isSemiringMonomorphism_1460 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.injective
d_injective_1488 ::
  T_IsSemiringIsomorphism_1452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1488 v0
  = coe d_injective_1412 (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1490 ::
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1490 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe
         d_isSemiringHomomorphism_1410
         (coe d_isSemiringMonomorphism_1460 (coe v0)))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_1492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringMonomorphism_1012
d_isNearSemiringMonomorphism_1492 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringMonomorphism_1492 v7
du_isNearSemiringMonomorphism_1492 ::
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringMonomorphism_1012
du_isNearSemiringMonomorphism_1492 v0
  = coe
      du_isNearSemiringMonomorphism_1438
      (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_1494 ::
  T_IsSemiringIsomorphism_1452 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1494 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_1410
                  (coe d_isSemiringMonomorphism_1460 (coe v0))))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.isSemiringHomomorphism
d_isSemiringHomomorphism_1496 ::
  T_IsSemiringIsomorphism_1452 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_1496 v0
  = coe
      d_isSemiringHomomorphism_1410
      (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.cong
d_cong_1498 ::
  T_IsSemiringIsomorphism_1452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1498 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe
                     d_isSemiringHomomorphism_1410
                     (coe d_isSemiringMonomorphism_1460 (coe v0)))))))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism.isNearSemiringIsomorphism
d_isNearSemiringIsomorphism_1500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringIsomorphism_1056
d_isNearSemiringIsomorphism_1500 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringIsomorphism_1500 v7
du_isNearSemiringIsomorphism_1500 ::
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringIsomorphism_1056
du_isNearSemiringIsomorphism_1500 v0
  = coe
      C_constructor_1108
      (coe
         du_isNearSemiringMonomorphism_1438
         (coe d_isSemiringMonomorphism_1460 (coe v0)))
      (coe d_surjective_1462 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_1504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaIsomorphism_240
d_'42''45'isMagmaIsomorphism_1504 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaIsomorphism_1504 v7
du_'42''45'isMagmaIsomorphism_1504 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaIsomorphism_240
du_'42''45'isMagmaIsomorphism_1504 v0
  = coe
      du_'42''45'isMagmaIsomorphism_1106
      (coe du_isNearSemiringIsomorphism_1500 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism._.+-isMonoidIsomorphism
d_'43''45'isMonoidIsomorphism_1506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
d_'43''45'isMonoidIsomorphism_1506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidIsomorphism_1506 v7
du_'43''45'isMonoidIsomorphism_1506 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
du_'43''45'isMonoidIsomorphism_1506 v0
  = coe
      du_'43''45'isMonoidIsomorphism_1098
      (coe du_isNearSemiringIsomorphism_1500 (coe v0))
-- Algebra.Morphism.Structures.SemiringMorphisms.IsSemiringIsomorphism.*-isMonoidIsomorphism
d_'42''45'isMonoidIsomorphism_1508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
d_'42''45'isMonoidIsomorphism_1508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidIsomorphism_1508 v7
du_'42''45'isMonoidIsomorphism_1508 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
du_'42''45'isMonoidIsomorphism_1508 v0
  = coe
      C_constructor_476
      (coe
         du_'42''45'isMonoidMonomorphism_1446
         (coe d_isSemiringMonomorphism_1460 (coe v0)))
      (coe d_surjective_1462 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms._._*_
d__'42'__1528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'42'__1528 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'42'__1528 v4
du__'42'__1528 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'42'__1528 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__264 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms._._≈_
d__'8776'__1532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1532 = erased
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms._.Carrier
d_Carrier_1548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 -> ()
d_Carrier_1548 = erased
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism
d_IsGroupHomomorphism_1580 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism
d_IsGroupIsomorphism_1584 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism
d_IsGroupMonomorphism_1588 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.homo
d_homo_1594 ::
  T_IsGroupHomomorphism_670 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1594 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_678 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1596 ::
  T_IsGroupHomomorphism_670 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1596 v0
  = coe
      d_isMagmaHomomorphism_388 (coe d_isMonoidHomomorphism_678 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1598 ::
  T_IsGroupHomomorphism_670 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_1598 v0
  = coe d_isMonoidHomomorphism_678 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.isRelHomomorphism
d_isRelHomomorphism_1600 ::
  T_IsGroupHomomorphism_670 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1600 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_678 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.ε-homo
d_ε'45'homo_1602 :: T_IsGroupHomomorphism_670 -> AgdaAny
d_ε'45'homo_1602 v0
  = coe d_ε'45'homo_390 (coe d_isMonoidHomomorphism_678 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.⁻¹-homo
d_'8315''185''45'homo_1604 ::
  T_IsGroupHomomorphism_670 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1604 v0
  = coe d_'8315''185''45'homo_680 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupHomomorphism.cong
d_cong_1606 ::
  T_IsGroupHomomorphism_670 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1606 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_isMonoidHomomorphism_678 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.injective
d_injective_1610 ::
  T_IsGroupIsomorphism_738 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1610 v0
  = coe d_injective_708 (coe d_isGroupMonomorphism_746 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isGroupHomomorphism
d_isGroupHomomorphism_1612 ::
  T_IsGroupIsomorphism_738 -> T_IsGroupHomomorphism_670
d_isGroupHomomorphism_1612 v0
  = coe
      d_isGroupHomomorphism_706 (coe d_isGroupMonomorphism_746 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isGroupMonomorphism
d_isGroupMonomorphism_1614 ::
  T_IsGroupIsomorphism_738 -> T_IsGroupMonomorphism_698
d_isGroupMonomorphism_1614 v0
  = coe d_isGroupMonomorphism_746 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1616 ::
  T_IsGroupIsomorphism_738 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1616 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_isGroupHomomorphism_706
            (coe d_isGroupMonomorphism_746 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_1618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_1618 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_1618 v7
du_isMagmaIsomorphism_1618 ::
  T_IsGroupIsomorphism_738 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_1618 v0
  = coe
      du_isMagmaIsomorphism_470 (coe du_isMonoidIsomorphism_776 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1620 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1620 v7
du_isMagmaMonomorphism_1620 ::
  T_IsGroupIsomorphism_738 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1620 v0
  = let v1 = d_isGroupMonomorphism_746 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_428
         (coe du_isMonoidMonomorphism_726 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1622 ::
  T_IsGroupIsomorphism_738 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_1622 v0
  = coe
      d_isMonoidHomomorphism_678
      (coe
         d_isGroupHomomorphism_706 (coe d_isGroupMonomorphism_746 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMonoidIsomorphism
d_isMonoidIsomorphism_1624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMonoidIsomorphism_438
d_isMonoidIsomorphism_1624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMonoidIsomorphism_1624
du_isMonoidIsomorphism_1624 ::
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMonoidIsomorphism_438
du_isMonoidIsomorphism_1624 v0 v1
  = coe du_isMonoidIsomorphism_776 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_1626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_1626 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_1626 v7
du_isMonoidMonomorphism_1626 ::
  T_IsGroupIsomorphism_738 -> T_IsMonoidMonomorphism_404
du_isMonoidMonomorphism_1626 v0
  = coe
      du_isMonoidMonomorphism_726
      (coe d_isGroupMonomorphism_746 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isRelHomomorphism
d_isRelHomomorphism_1628 ::
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1628 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_isGroupHomomorphism_706
               (coe d_isGroupMonomorphism_746 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isRelIsomorphism
d_isRelIsomorphism_1630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_1630 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1630 v7
du_isRelIsomorphism_1630 ::
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_1630 v0
  = let v1 = coe du_isMonoidIsomorphism_776 (coe v0) in
    coe
      (coe
         du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.isRelMonomorphism
d_isRelMonomorphism_1632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1632 v7
du_isRelMonomorphism_1632 ::
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1632 v0
  = let v1 = d_isGroupMonomorphism_746 (coe v0) in
    coe
      (let v2 = coe du_isMonoidMonomorphism_726 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_234
            (coe du_isMagmaMonomorphism_428 (coe v2))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.surjective
d_surjective_1634 ::
  T_IsGroupIsomorphism_738 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1634 v0 = coe d_surjective_748 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.ε-homo
d_ε'45'homo_1636 :: T_IsGroupIsomorphism_738 -> AgdaAny
d_ε'45'homo_1636 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_isGroupHomomorphism_706
            (coe d_isGroupMonomorphism_746 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.⁻¹-homo
d_'8315''185''45'homo_1638 ::
  T_IsGroupIsomorphism_738 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1638 v0
  = coe
      d_'8315''185''45'homo_680
      (coe
         d_isGroupHomomorphism_706 (coe d_isGroupMonomorphism_746 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.homo
d_homo_1640 ::
  T_IsGroupIsomorphism_738 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1640 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_isGroupHomomorphism_706
               (coe d_isGroupMonomorphism_746 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupIsomorphism.cong
d_cong_1642 ::
  T_IsGroupIsomorphism_738 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1642 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe
                  d_isGroupHomomorphism_706
                  (coe d_isGroupMonomorphism_746 (coe v0))))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.injective
d_injective_1646 ::
  T_IsGroupMonomorphism_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1646 v0 = coe d_injective_708 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isGroupHomomorphism
d_isGroupHomomorphism_1648 ::
  T_IsGroupMonomorphism_698 -> T_IsGroupHomomorphism_670
d_isGroupHomomorphism_1648 v0
  = coe d_isGroupHomomorphism_706 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1650 ::
  T_IsGroupMonomorphism_698 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1650 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe d_isGroupHomomorphism_706 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_698 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1652 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1652 v7
du_isMagmaMonomorphism_1652 ::
  T_IsGroupMonomorphism_698 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1652 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe du_isMonoidMonomorphism_726 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_1654 ::
  T_IsGroupMonomorphism_698 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_1654 v0
  = coe
      d_isMonoidHomomorphism_678 (coe d_isGroupHomomorphism_706 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_1656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_698 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_1656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMonoidMonomorphism_1656
du_isMonoidMonomorphism_1656 ::
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_698 -> T_IsMonoidMonomorphism_404
du_isMonoidMonomorphism_1656 v0 v1
  = coe du_isMonoidMonomorphism_726 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isRelHomomorphism
d_isRelHomomorphism_1658 ::
  T_IsGroupMonomorphism_698 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1658 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe d_isGroupHomomorphism_706 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.isRelMonomorphism
d_isRelMonomorphism_1660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_698 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1660 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1660 v7
du_isRelMonomorphism_1660 ::
  T_IsGroupMonomorphism_698 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1660 v0
  = let v1 = coe du_isMonoidMonomorphism_726 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.ε-homo
d_ε'45'homo_1662 :: T_IsGroupMonomorphism_698 -> AgdaAny
d_ε'45'homo_1662 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe d_isGroupHomomorphism_706 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.⁻¹-homo
d_'8315''185''45'homo_1664 ::
  T_IsGroupMonomorphism_698 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1664 v0
  = coe
      d_'8315''185''45'homo_680 (coe d_isGroupHomomorphism_706 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.homo
d_homo_1666 ::
  T_IsGroupMonomorphism_698 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1666 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe d_isGroupHomomorphism_706 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+.IsGroupMonomorphism.cong
d_cong_1668 ::
  T_IsGroupMonomorphism_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1668 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe d_isGroupHomomorphism_706 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaHomomorphism
d_IsMagmaHomomorphism_1672 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism
d_IsMagmaIsomorphism_1676 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism
d_IsMagmaMonomorphism_1680 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaHomomorphism.homo
d_homo_1686 ::
  T_IsMagmaHomomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1686 v0 = coe d_homo_204 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_1688 ::
  T_IsMagmaHomomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1688 v0 = coe d_isRelHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaHomomorphism.cong
d_cong_1690 ::
  T_IsMagmaHomomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1690 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.homo
d_homo_1694 ::
  T_IsMagmaIsomorphism_240 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1694 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.injective
d_injective_1696 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1696 v0
  = coe d_injective_224 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1698 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1698 v0
  = coe
      d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1700 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1700 v0
  = coe d_isMagmaMonomorphism_248 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_1702 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1702 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_1704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_1704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_1704
du_isRelIsomorphism_1704 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_1704 v0 v1 = coe du_isRelIsomorphism_266 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_1706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1706 v7
du_isRelMonomorphism_1706 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1706 v0
  = coe
      du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.surjective
d_surjective_1708 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1708 v0 = coe d_surjective_250 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaIsomorphism.cong
d_cong_1710 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1710 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_222
            (coe d_isMagmaMonomorphism_248 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.homo
d_homo_1714 ::
  T_IsMagmaMonomorphism_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1714 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.injective
d_injective_1716 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1716 v0 = coe d_injective_224 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1718 ::
  T_IsMagmaMonomorphism_214 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1718 v0
  = coe d_isMagmaHomomorphism_222 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_1720 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1720 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_1722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1722 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_1722
du_isRelMonomorphism_1722 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1722 v0 v1 = coe du_isRelMonomorphism_234 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.*.IsMagmaMonomorphism.cong
d_cong_1724 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1724 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringHomomorphism
d_IsNearSemiringHomomorphism_1728 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism
d_IsNearSemiringIsomorphism_1732 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism
d_IsNearSemiringMonomorphism_1736 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringHomomorphism.*-homo
d_'42''45'homo_1742 ::
  T_IsNearSemiringHomomorphism_982 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1742 v0 = coe d_'42''45'homo_992 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringHomomorphism_982 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1744 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaHomomorphism_1744
du_'42''45'isMagmaHomomorphism_1744 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringHomomorphism_982 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1744 v0 v1
  = coe du_'42''45'isMagmaHomomorphism_1006 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringHomomorphism.homo
d_homo_1746 ::
  T_IsNearSemiringHomomorphism_982 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1746 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe d_'43''45'isMonoidHomomorphism_990 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1748 ::
  T_IsNearSemiringHomomorphism_982 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1748 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe d_'43''45'isMonoidHomomorphism_990 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringHomomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1750 ::
  T_IsNearSemiringHomomorphism_982 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_1750 v0
  = coe d_'43''45'isMonoidHomomorphism_990 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringHomomorphism.ε-homo
d_ε'45'homo_1752 :: T_IsNearSemiringHomomorphism_982 -> AgdaAny
d_ε'45'homo_1752 v0
  = coe
      d_ε'45'homo_390 (coe d_'43''45'isMonoidHomomorphism_990 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringHomomorphism.isRelHomomorphism
d_isRelHomomorphism_1754 ::
  T_IsNearSemiringHomomorphism_982 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1754 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe d_'43''45'isMonoidHomomorphism_990 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringHomomorphism.cong
d_cong_1756 ::
  T_IsNearSemiringHomomorphism_982 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1756 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_'43''45'isMonoidHomomorphism_990 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.*-homo
d_'42''45'homo_1760 ::
  T_IsNearSemiringIsomorphism_1056 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1760 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1020
         (coe d_isNearSemiringMonomorphism_1064 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1762 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1762 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1762 v7
du_'42''45'isMagmaHomomorphism_1762 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1762 v0
  = let v1 = d_isNearSemiringMonomorphism_1064 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_1006
         (coe d_isNearSemiringHomomorphism_1020 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_1764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
d_'42''45'isMagmaIsomorphism_1764 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaIsomorphism_1764
du_'42''45'isMagmaIsomorphism_1764 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
du_'42''45'isMagmaIsomorphism_1764 v0 v1
  = coe du_'42''45'isMagmaIsomorphism_1106 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_1766 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1766 v7
du_'42''45'isMagmaMonomorphism_1766 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_1766 v0
  = coe
      du_'42''45'isMagmaMonomorphism_1050
      (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.homo
d_homo_1768 ::
  T_IsNearSemiringIsomorphism_1056 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1768 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1020
               (coe d_isNearSemiringMonomorphism_1064 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1770 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1770 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1020
            (coe d_isNearSemiringMonomorphism_1064 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_1772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_1772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_1772 v7
du_isMagmaIsomorphism_1772 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_1772 v0
  = coe
      du_isMagmaIsomorphism_470
      (coe du_'43''45'isMonoidIsomorphism_1098 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1774 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1774 v7
du_isMagmaMonomorphism_1774 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1774 v0
  = let v1 = d_isNearSemiringMonomorphism_1064 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_428
         (coe du_'43''45'isMonoidMonomorphism_1042 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1776 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_1776 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1020
         (coe d_isNearSemiringMonomorphism_1064 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.+-isMonoidIsomorphism
d_'43''45'isMonoidIsomorphism_1778 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidIsomorphism_438
d_'43''45'isMonoidIsomorphism_1778 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'43''45'isMonoidIsomorphism_1778
du_'43''45'isMonoidIsomorphism_1778 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidIsomorphism_438
du_'43''45'isMonoidIsomorphism_1778 v0 v1
  = coe du_'43''45'isMonoidIsomorphism_1098 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_1780 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_1780 v7
du_'43''45'isMonoidMonomorphism_1780 ::
  T_IsNearSemiringIsomorphism_1056 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_1780 v0
  = coe
      du_'43''45'isMonoidMonomorphism_1042
      (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.ε-homo
d_ε'45'homo_1782 :: T_IsNearSemiringIsomorphism_1056 -> AgdaAny
d_ε'45'homo_1782 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1020
            (coe d_isNearSemiringMonomorphism_1064 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.injective
d_injective_1784 ::
  T_IsNearSemiringIsomorphism_1056 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1784 v0
  = coe
      d_injective_1022 (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1786 ::
  T_IsNearSemiringIsomorphism_1056 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1786 v0
  = coe
      d_isNearSemiringHomomorphism_1020
      (coe d_isNearSemiringMonomorphism_1064 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_1788 ::
  T_IsNearSemiringIsomorphism_1056 ->
  T_IsNearSemiringMonomorphism_1012
d_isNearSemiringMonomorphism_1788 v0
  = coe d_isNearSemiringMonomorphism_1064 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.isRelHomomorphism
d_isRelHomomorphism_1790 ::
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1790 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1020
               (coe d_isNearSemiringMonomorphism_1064 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.isRelIsomorphism
d_isRelIsomorphism_1792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_1792 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1792 v7
du_isRelIsomorphism_1792 ::
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_1792 v0
  = let v1 = coe du_'43''45'isMonoidIsomorphism_1098 (coe v0) in
    coe
      (coe
         du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.isRelMonomorphism
d_isRelMonomorphism_1794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1794 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1794 v7
du_isRelMonomorphism_1794 ::
  T_IsNearSemiringIsomorphism_1056 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1794 v0
  = let v1 = d_isNearSemiringMonomorphism_1064 (coe v0) in
    coe
      (let v2 = coe du_'43''45'isMonoidMonomorphism_1042 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_234
            (coe du_isMagmaMonomorphism_428 (coe v2))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.surjective
d_surjective_1796 ::
  T_IsNearSemiringIsomorphism_1056 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1796 v0 = coe d_surjective_1066 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringIsomorphism.cong
d_cong_1798 ::
  T_IsNearSemiringIsomorphism_1056 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1798 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1020
                  (coe d_isNearSemiringMonomorphism_1064 (coe v0))))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.*-homo
d_'42''45'homo_1802 ::
  T_IsNearSemiringMonomorphism_1012 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1802 v0
  = coe
      d_'42''45'homo_992 (coe d_isNearSemiringHomomorphism_1020 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1804 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1804 v7
du_'42''45'isMagmaHomomorphism_1804 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1804 v0
  = coe
      du_'42''45'isMagmaHomomorphism_1006
      (coe d_isNearSemiringHomomorphism_1020 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_1806 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaMonomorphism_1806
du_'42''45'isMagmaMonomorphism_1806 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_1806 v0 v1
  = coe du_'42''45'isMagmaMonomorphism_1050 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.homo
d_homo_1808 ::
  T_IsNearSemiringMonomorphism_1012 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1808 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1020 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_1810 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1810 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1020 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_1812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1812 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1812 v7
du_isMagmaMonomorphism_1812 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1812 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe du_'43''45'isMonoidMonomorphism_1042 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_1814 ::
  T_IsNearSemiringMonomorphism_1012 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_1814 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe d_isNearSemiringHomomorphism_1020 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_1816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_1816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'43''45'isMonoidMonomorphism_1816
du_'43''45'isMonoidMonomorphism_1816 ::
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_1816 v0 v1
  = coe du_'43''45'isMonoidMonomorphism_1042 v1
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.ε-homo
d_ε'45'homo_1818 :: T_IsNearSemiringMonomorphism_1012 -> AgdaAny
d_ε'45'homo_1818 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1020 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.injective
d_injective_1820 ::
  T_IsNearSemiringMonomorphism_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1820 v0 = coe d_injective_1022 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1822 ::
  T_IsNearSemiringMonomorphism_1012 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1822 v0
  = coe d_isNearSemiringHomomorphism_1020 (coe v0)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.isRelHomomorphism
d_isRelHomomorphism_1824 ::
  T_IsNearSemiringMonomorphism_1012 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1824 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1020 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.isRelMonomorphism
d_isRelMonomorphism_1826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearSemiringMonomorphism_1012 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1826 v7
du_isRelMonomorphism_1826 ::
  T_IsNearSemiringMonomorphism_1012 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1826 v0
  = let v1 = coe du_'43''45'isMonoidMonomorphism_1042 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.+*.IsNearSemiringMonomorphism.cong
d_cong_1828 ::
  T_IsNearSemiringMonomorphism_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1828 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe d_isNearSemiringHomomorphism_1020 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms._.Homomorphic₂
d_Homomorphic'8322'_1836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_1836 = erased
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism
d_IsRingWithoutOneHomomorphism_1842 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingWithoutOneHomomorphism_1842
  = C_constructor_1874 T_IsGroupHomomorphism_670
                       (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_1850 ::
  T_IsRingWithoutOneHomomorphism_1842 -> T_IsGroupHomomorphism_670
d_'43''45'isGroupHomomorphism_1850 v0
  = case coe v0 of
      C_constructor_1874 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism.*-homo
d_'42''45'homo_1852 ::
  T_IsRingWithoutOneHomomorphism_1842 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1852 v0
  = case coe v0 of
      C_constructor_1874 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.homo
d_homo_1856 ::
  T_IsRingWithoutOneHomomorphism_1842 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_homo_1856 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe d_'43''45'isGroupHomomorphism_1850 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1858 ::
  T_IsRingWithoutOneHomomorphism_1842 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1858 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe d_'43''45'isGroupHomomorphism_1850 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_1860 ::
  T_IsRingWithoutOneHomomorphism_1842 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_1860 v0
  = coe
      d_isMonoidHomomorphism_678
      (coe d_'43''45'isGroupHomomorphism_1850 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.ε-homo
d_ε'45'homo_1862 :: T_IsRingWithoutOneHomomorphism_1842 -> AgdaAny
d_ε'45'homo_1862 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe d_'43''45'isGroupHomomorphism_1850 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_1864 ::
  T_IsRingWithoutOneHomomorphism_1842 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1864 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe d_'43''45'isGroupHomomorphism_1850 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.⁻¹-homo
d_'8315''185''45'homo_1866 ::
  T_IsRingWithoutOneHomomorphism_1842 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1866 v0
  = coe
      d_'8315''185''45'homo_680
      (coe d_'43''45'isGroupHomomorphism_1850 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism._.cong
d_cong_1868 ::
  T_IsRingWithoutOneHomomorphism_1842 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1868 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe d_'43''45'isGroupHomomorphism_1850 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneHomomorphism_1842 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1870 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringHomomorphism_1870 v7
du_isNearSemiringHomomorphism_1870 ::
  T_IsRingWithoutOneHomomorphism_1842 ->
  T_IsNearSemiringHomomorphism_982
du_isNearSemiringHomomorphism_1870 v0
  = coe
      C_constructor_1008
      (coe
         d_isMonoidHomomorphism_678
         (coe d_'43''45'isGroupHomomorphism_1850 (coe v0)))
      (coe d_'42''45'homo_1852 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneHomomorphism_1842 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1872 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1872 v7
du_'42''45'isMagmaHomomorphism_1872 ::
  T_IsRingWithoutOneHomomorphism_1842 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1872 v0
  = coe
      C_constructor_210
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe d_'43''45'isGroupHomomorphism_1850 (coe v0)))))
      (coe d_'42''45'homo_1852 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism
d_IsRingWithoutOneMonomorphism_1878 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingWithoutOneMonomorphism_1878
  = C_constructor_1926 T_IsRingWithoutOneHomomorphism_1842
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism.isRingWithoutOneHomomorphism
d_isRingWithoutOneHomomorphism_1886 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  T_IsRingWithoutOneHomomorphism_1842
d_isRingWithoutOneHomomorphism_1886 v0
  = case coe v0 of
      C_constructor_1926 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism.injective
d_injective_1888 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1888 v0
  = case coe v0 of
      C_constructor_1926 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.*-homo
d_'42''45'homo_1892 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1892 v0
  = coe
      d_'42''45'homo_1852
      (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1894 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1894 v7
du_'42''45'isMagmaHomomorphism_1894 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1894 v0
  = coe
      du_'42''45'isMagmaHomomorphism_1872
      (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.homo
d_homo_1896 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_homo_1896 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_'43''45'isGroupHomomorphism_1850
               (coe d_isRingWithoutOneHomomorphism_1886 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_1898 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsGroupHomomorphism_670
d_'43''45'isGroupHomomorphism_1898 v0
  = coe
      d_'43''45'isGroupHomomorphism_1850
      (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1900 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1900 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_'43''45'isGroupHomomorphism_1850
            (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_1902 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_1902 v0
  = coe
      d_isMonoidHomomorphism_678
      (coe
         d_'43''45'isGroupHomomorphism_1850
         (coe d_isRingWithoutOneHomomorphism_1886 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.ε-homo
d_ε'45'homo_1904 :: T_IsRingWithoutOneMonomorphism_1878 -> AgdaAny
d_ε'45'homo_1904 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_'43''45'isGroupHomomorphism_1850
            (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1906 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringHomomorphism_1906 v7
du_isNearSemiringHomomorphism_1906 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  T_IsNearSemiringHomomorphism_982
du_isNearSemiringHomomorphism_1906 v0
  = coe
      du_isNearSemiringHomomorphism_1870
      (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_1908 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1908 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_'43''45'isGroupHomomorphism_1850
               (coe d_isRingWithoutOneHomomorphism_1886 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.⁻¹-homo
d_'8315''185''45'homo_1910 ::
  T_IsRingWithoutOneMonomorphism_1878 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1910 v0
  = coe
      d_'8315''185''45'homo_680
      (coe
         d_'43''45'isGroupHomomorphism_1850
         (coe d_isRingWithoutOneHomomorphism_1886 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.cong
d_cong_1912 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1912 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe
                  d_'43''45'isGroupHomomorphism_1850
                  (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism.+-isGroupMonomorphism
d_'43''45'isGroupMonomorphism_1914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsGroupMonomorphism_698
d_'43''45'isGroupMonomorphism_1914 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupMonomorphism_1914 v7
du_'43''45'isGroupMonomorphism_1914 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsGroupMonomorphism_698
du_'43''45'isGroupMonomorphism_1914 v0
  = coe
      C_constructor_734
      (coe
         d_'43''45'isGroupHomomorphism_1850
         (coe d_isRingWithoutOneHomomorphism_1886 (coe v0)))
      (coe d_injective_1888 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_1918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1918 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1918 v7
du_isMagmaMonomorphism_1918 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1918 v0
  = let v1 = coe du_'43''45'isGroupMonomorphism_1914 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_428
         (coe du_isMonoidMonomorphism_726 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isMonoidMonomorphism
d_isMonoidMonomorphism_1920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_1920 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_1920 v7
du_isMonoidMonomorphism_1920 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMonoidMonomorphism_404
du_isMonoidMonomorphism_1920 v0
  = coe
      du_isMonoidMonomorphism_726
      (coe du_'43''45'isGroupMonomorphism_1914 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_1922 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1922 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1922 v7
du_isRelMonomorphism_1922 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1922 v0
  = let v1 = coe du_'43''45'isGroupMonomorphism_1914 (coe v0) in
    coe
      (let v2 = coe du_isMonoidMonomorphism_726 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_234
            (coe du_isMagmaMonomorphism_428 (coe v2))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_1924 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1924 v7
du_'42''45'isMagmaMonomorphism_1924 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_1924 v0
  = coe
      C_constructor_236
      (coe
         du_'42''45'isMagmaHomomorphism_1872
         (coe d_isRingWithoutOneHomomorphism_1886 (coe v0)))
      (coe d_injective_1888 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism
d_IsRingWithoutOneIsoMorphism_1930 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingWithoutOneIsoMorphism_1930
  = C_constructor_1992 T_IsRingWithoutOneMonomorphism_1878
                       (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism.isRingWithoutOneMonomorphism
d_isRingWithoutOneMonomorphism_1938 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  T_IsRingWithoutOneMonomorphism_1878
d_isRingWithoutOneMonomorphism_1938 v0
  = case coe v0 of
      C_constructor_1992 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism.surjective
d_surjective_1940 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1940 v0
  = case coe v0 of
      C_constructor_1992 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.*-homo
d_'42''45'homo_1944 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_1944 v0
  = coe
      d_'42''45'homo_1852
      (coe
         d_isRingWithoutOneHomomorphism_1886
         (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_1946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_1946 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_1946 v7
du_'42''45'isMagmaHomomorphism_1946 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_1946 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1938 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_1872
         (coe d_isRingWithoutOneHomomorphism_1886 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_1948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_1948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_1948 v7
du_'42''45'isMagmaMonomorphism_1948 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_1948 v0
  = coe
      du_'42''45'isMagmaMonomorphism_1924
      (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.homo
d_homo_1950 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_1950 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_'43''45'isGroupHomomorphism_1850
               (coe
                  d_isRingWithoutOneHomomorphism_1886
                  (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_1952 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsGroupHomomorphism_670
d_'43''45'isGroupHomomorphism_1952 v0
  = coe
      d_'43''45'isGroupHomomorphism_1850
      (coe
         d_isRingWithoutOneHomomorphism_1886
         (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.+-isGroupMonomorphism
d_'43''45'isGroupMonomorphism_1954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsGroupMonomorphism_698
d_'43''45'isGroupMonomorphism_1954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupMonomorphism_1954 v7
du_'43''45'isGroupMonomorphism_1954 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsGroupMonomorphism_698
du_'43''45'isGroupMonomorphism_1954 v0
  = coe
      du_'43''45'isGroupMonomorphism_1914
      (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_1956 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_1956 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_'43''45'isGroupHomomorphism_1850
            (coe
               d_isRingWithoutOneHomomorphism_1886
               (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_1958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_1958 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_1958 v7
du_isMagmaMonomorphism_1958 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_1958 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1938 (coe v0) in
    coe
      (let v2 = coe du_'43''45'isGroupMonomorphism_1914 (coe v1) in
       coe
         (coe
            du_isMagmaMonomorphism_428
            (coe du_isMonoidMonomorphism_726 (coe v2))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMonoidHomomorphism
d_isMonoidHomomorphism_1960 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_1960 v0
  = coe
      d_isMonoidHomomorphism_678
      (coe
         d_'43''45'isGroupHomomorphism_1850
         (coe
            d_isRingWithoutOneHomomorphism_1886
            (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMonoidMonomorphism
d_isMonoidMonomorphism_1962 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_1962 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_1962 v7
du_isMonoidMonomorphism_1962 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMonoidMonomorphism_404
du_isMonoidMonomorphism_1962 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1938 (coe v0) in
    coe
      (coe
         du_isMonoidMonomorphism_726
         (coe du_'43''45'isGroupMonomorphism_1914 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.ε-homo
d_ε'45'homo_1964 :: T_IsRingWithoutOneIsoMorphism_1930 -> AgdaAny
d_ε'45'homo_1964 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_'43''45'isGroupHomomorphism_1850
            (coe
               d_isRingWithoutOneHomomorphism_1886
               (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.injective
d_injective_1966 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1966 v0
  = coe
      d_injective_1888 (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_1968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_1968 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringHomomorphism_1968 v7
du_isNearSemiringHomomorphism_1968 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  T_IsNearSemiringHomomorphism_982
du_isNearSemiringHomomorphism_1968 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1938 (coe v0) in
    coe
      (coe
         du_isNearSemiringHomomorphism_1870
         (coe d_isRingWithoutOneHomomorphism_1886 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isRelHomomorphism
d_isRelHomomorphism_1970 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_1970 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_'43''45'isGroupHomomorphism_1850
               (coe
                  d_isRingWithoutOneHomomorphism_1886
                  (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isRelMonomorphism
d_isRelMonomorphism_1972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_1972 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_1972 v7
du_isRelMonomorphism_1972 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_1972 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1938 (coe v0) in
    coe
      (let v2 = coe du_'43''45'isGroupMonomorphism_1914 (coe v1) in
       coe
         (let v3 = coe du_isMonoidMonomorphism_726 (coe v2) in
          coe
            (coe
               du_isRelMonomorphism_234
               (coe du_isMagmaMonomorphism_428 (coe v3)))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isRingWithoutOneHomomorphism
d_isRingWithoutOneHomomorphism_1974 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  T_IsRingWithoutOneHomomorphism_1842
d_isRingWithoutOneHomomorphism_1974 v0
  = coe
      d_isRingWithoutOneHomomorphism_1886
      (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.⁻¹-homo
d_'8315''185''45'homo_1976 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1976 v0
  = coe
      d_'8315''185''45'homo_680
      (coe
         d_'43''45'isGroupHomomorphism_1850
         (coe
            d_isRingWithoutOneHomomorphism_1886
            (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.cong
d_cong_1978 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1978 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe
                  d_'43''45'isGroupHomomorphism_1850
                  (coe
                     d_isRingWithoutOneHomomorphism_1886
                     (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism.+-isGroupIsomorphism
d_'43''45'isGroupIsomorphism_1980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsGroupIsomorphism_738
d_'43''45'isGroupIsomorphism_1980 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupIsomorphism_1980 v7
du_'43''45'isGroupIsomorphism_1980 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsGroupIsomorphism_738
du_'43''45'isGroupIsomorphism_1980 v0
  = coe
      C_constructor_784
      (coe
         du_'43''45'isGroupMonomorphism_1914
         (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))
      (coe d_surjective_1940 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMagmaIsomorphism
d_isMagmaIsomorphism_1984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_1984 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_1984 v7
du_isMagmaIsomorphism_1984 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_1984 v0
  = let v1 = coe du_'43''45'isGroupIsomorphism_1980 (coe v0) in
    coe
      (coe
         du_isMagmaIsomorphism_470
         (coe du_isMonoidIsomorphism_776 (coe v1)))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isMonoidIsomorphism
d_isMonoidIsomorphism_1986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMonoidIsomorphism_438
d_isMonoidIsomorphism_1986 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidIsomorphism_1986 v7
du_isMonoidIsomorphism_1986 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMonoidIsomorphism_438
du_isMonoidIsomorphism_1986 v0
  = coe
      du_isMonoidIsomorphism_776
      (coe du_'43''45'isGroupIsomorphism_1980 (coe v0))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism._.isRelIsomorphism
d_isRelIsomorphism_1988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_1988 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_1988 v7
du_isRelIsomorphism_1988 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_1988 v0
  = let v1 = coe du_'43''45'isGroupIsomorphism_1980 (coe v0) in
    coe
      (let v2 = coe du_isMonoidIsomorphism_776 (coe v1) in
       coe
         (coe
            du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v2))))
-- Algebra.Morphism.Structures.RingWithoutOneMorphisms.IsRingWithoutOneIsoMorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_1990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRingWithoutOne_240 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaIsomorphism_240
d_'42''45'isMagmaIsomorphism_1990 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaIsomorphism_1990 v7
du_'42''45'isMagmaIsomorphism_1990 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaIsomorphism_240
du_'42''45'isMagmaIsomorphism_1990 v0
  = coe
      C_constructor_268
      (coe
         du_'42''45'isMagmaMonomorphism_1924
         (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))
      (coe d_surjective_1940 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._._≈_
d__'8776'__2014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__2014 = erased
-- Algebra.Morphism.Structures.RingMorphisms._.-_
d_'45'__2028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  AgdaAny -> AgdaAny
d_'45'__2028 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_'45'__2028 v4
du_'45'__2028 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  AgdaAny -> AgdaAny
du_'45'__2028 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__318 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.Carrier
d_Carrier_2034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 -> ()
d_Carrier_2034 = erased
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism
d_IsGroupHomomorphism_2074 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism
d_IsGroupIsomorphism_2078 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism
d_IsGroupMonomorphism_2082 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.homo
d_homo_2088 ::
  T_IsGroupHomomorphism_670 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2088 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_678 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2090 ::
  T_IsGroupHomomorphism_670 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2090 v0
  = coe
      d_isMagmaHomomorphism_388 (coe d_isMonoidHomomorphism_678 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_2092 ::
  T_IsGroupHomomorphism_670 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_2092 v0
  = coe d_isMonoidHomomorphism_678 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2094 ::
  T_IsGroupHomomorphism_670 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2094 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_678 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.ε-homo
d_ε'45'homo_2096 :: T_IsGroupHomomorphism_670 -> AgdaAny
d_ε'45'homo_2096 v0
  = coe d_ε'45'homo_390 (coe d_isMonoidHomomorphism_678 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.⁻¹-homo
d_'8315''185''45'homo_2098 ::
  T_IsGroupHomomorphism_670 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_2098 v0
  = coe d_'8315''185''45'homo_680 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupHomomorphism.cong
d_cong_2100 ::
  T_IsGroupHomomorphism_670 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2100 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_isMonoidHomomorphism_678 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.injective
d_injective_2104 ::
  T_IsGroupIsomorphism_738 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2104 v0
  = coe d_injective_708 (coe d_isGroupMonomorphism_746 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isGroupHomomorphism
d_isGroupHomomorphism_2106 ::
  T_IsGroupIsomorphism_738 -> T_IsGroupHomomorphism_670
d_isGroupHomomorphism_2106 v0
  = coe
      d_isGroupHomomorphism_706 (coe d_isGroupMonomorphism_746 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isGroupMonomorphism
d_isGroupMonomorphism_2108 ::
  T_IsGroupIsomorphism_738 -> T_IsGroupMonomorphism_698
d_isGroupMonomorphism_2108 v0
  = coe d_isGroupMonomorphism_746 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2110 ::
  T_IsGroupIsomorphism_738 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2110 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_isGroupHomomorphism_706
            (coe d_isGroupMonomorphism_746 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_2112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_2112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_2112 v7
du_isMagmaIsomorphism_2112 ::
  T_IsGroupIsomorphism_738 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_2112 v0
  = coe
      du_isMagmaIsomorphism_470 (coe du_isMonoidIsomorphism_776 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_2114 v7
du_isMagmaMonomorphism_2114 ::
  T_IsGroupIsomorphism_738 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_2114 v0
  = let v1 = d_isGroupMonomorphism_746 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_428
         (coe du_isMonoidMonomorphism_726 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_2116 ::
  T_IsGroupIsomorphism_738 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_2116 v0
  = coe
      d_isMonoidHomomorphism_678
      (coe
         d_isGroupHomomorphism_706 (coe d_isGroupMonomorphism_746 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMonoidIsomorphism
d_isMonoidIsomorphism_2118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMonoidIsomorphism_438
d_isMonoidIsomorphism_2118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMonoidIsomorphism_2118
du_isMonoidIsomorphism_2118 ::
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMonoidIsomorphism_438
du_isMonoidIsomorphism_2118 v0 v1
  = coe du_isMonoidIsomorphism_776 v1
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_2120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_2120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_2120 v7
du_isMonoidMonomorphism_2120 ::
  T_IsGroupIsomorphism_738 -> T_IsMonoidMonomorphism_404
du_isMonoidMonomorphism_2120 v0
  = coe
      du_isMonoidMonomorphism_726
      (coe d_isGroupMonomorphism_746 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2122 ::
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2122 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_isGroupHomomorphism_706
               (coe d_isGroupMonomorphism_746 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_2124 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_2124 v7
du_isRelIsomorphism_2124 ::
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_2124 v0
  = let v1 = coe du_isMonoidIsomorphism_776 (coe v0) in
    coe
      (coe
         du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2126 v7
du_isRelMonomorphism_2126 ::
  T_IsGroupIsomorphism_738 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2126 v0
  = let v1 = d_isGroupMonomorphism_746 (coe v0) in
    coe
      (let v2 = coe du_isMonoidMonomorphism_726 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_234
            (coe du_isMagmaMonomorphism_428 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.surjective
d_surjective_2128 ::
  T_IsGroupIsomorphism_738 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2128 v0 = coe d_surjective_748 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.ε-homo
d_ε'45'homo_2130 :: T_IsGroupIsomorphism_738 -> AgdaAny
d_ε'45'homo_2130 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_isGroupHomomorphism_706
            (coe d_isGroupMonomorphism_746 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.⁻¹-homo
d_'8315''185''45'homo_2132 ::
  T_IsGroupIsomorphism_738 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_2132 v0
  = coe
      d_'8315''185''45'homo_680
      (coe
         d_isGroupHomomorphism_706 (coe d_isGroupMonomorphism_746 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.homo
d_homo_2134 ::
  T_IsGroupIsomorphism_738 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2134 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_isGroupHomomorphism_706
               (coe d_isGroupMonomorphism_746 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupIsomorphism.cong
d_cong_2136 ::
  T_IsGroupIsomorphism_738 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2136 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe
                  d_isGroupHomomorphism_706
                  (coe d_isGroupMonomorphism_746 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.injective
d_injective_2140 ::
  T_IsGroupMonomorphism_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2140 v0 = coe d_injective_708 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isGroupHomomorphism
d_isGroupHomomorphism_2142 ::
  T_IsGroupMonomorphism_698 -> T_IsGroupHomomorphism_670
d_isGroupHomomorphism_2142 v0
  = coe d_isGroupHomomorphism_706 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2144 ::
  T_IsGroupMonomorphism_698 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2144 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe d_isGroupHomomorphism_706 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_698 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_2146 v7
du_isMagmaMonomorphism_2146 ::
  T_IsGroupMonomorphism_698 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_2146 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe du_isMonoidMonomorphism_726 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_2148 ::
  T_IsGroupMonomorphism_698 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_2148 v0
  = coe
      d_isMonoidHomomorphism_678 (coe d_isGroupHomomorphism_706 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_2150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_698 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_2150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMonoidMonomorphism_2150
du_isMonoidMonomorphism_2150 ::
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_698 -> T_IsMonoidMonomorphism_404
du_isMonoidMonomorphism_2150 v0 v1
  = coe du_isMonoidMonomorphism_726 v1
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2152 ::
  T_IsGroupMonomorphism_698 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2152 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe d_isGroupHomomorphism_706 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroupMonomorphism_698 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2154 v7
du_isRelMonomorphism_2154 ::
  T_IsGroupMonomorphism_698 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2154 v0
  = let v1 = coe du_isMonoidMonomorphism_726 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.ε-homo
d_ε'45'homo_2156 :: T_IsGroupMonomorphism_698 -> AgdaAny
d_ε'45'homo_2156 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe d_isGroupHomomorphism_706 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.⁻¹-homo
d_'8315''185''45'homo_2158 ::
  T_IsGroupMonomorphism_698 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_2158 v0
  = coe
      d_'8315''185''45'homo_680 (coe d_isGroupHomomorphism_706 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.homo
d_homo_2160 ::
  T_IsGroupMonomorphism_698 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2160 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe d_isGroupHomomorphism_706 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.+.IsGroupMonomorphism.cong
d_cong_2162 ::
  T_IsGroupMonomorphism_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2162 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe d_isGroupHomomorphism_706 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism
d_IsMonoidHomomorphism_2166 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism
d_IsMonoidIsomorphism_2170 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism
d_IsMonoidMonomorphism_2174 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism.homo
d_homo_2180 ::
  T_IsMonoidHomomorphism_380 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2180 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_388 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2182 ::
  T_IsMonoidHomomorphism_380 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2182 v0
  = coe d_isMagmaHomomorphism_388 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2184 ::
  T_IsMonoidHomomorphism_380 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2184 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_388 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism.ε-homo
d_ε'45'homo_2186 :: T_IsMonoidHomomorphism_380 -> AgdaAny
d_ε'45'homo_2186 v0 = coe d_ε'45'homo_390 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidHomomorphism.cong
d_cong_2188 ::
  T_IsMonoidHomomorphism_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2188 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_388 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.homo
d_homo_2192 ::
  T_IsMonoidIsomorphism_438 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2192 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_412
            (coe d_isMonoidMonomorphism_446 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.injective
d_injective_2194 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2194 v0
  = coe d_injective_414 (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2196 ::
  T_IsMonoidIsomorphism_438 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2196 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_412
         (coe d_isMonoidMonomorphism_446 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_2198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_2198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaIsomorphism_2198
du_isMagmaIsomorphism_2198 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_2198 v0 v1 = coe du_isMagmaIsomorphism_470 v1
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_2200 v7
du_isMagmaMonomorphism_2200 ::
  T_IsMonoidIsomorphism_438 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_2200 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_2202 ::
  T_IsMonoidIsomorphism_438 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_2202 v0
  = coe
      d_isMonoidHomomorphism_412
      (coe d_isMonoidMonomorphism_446 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_2204 ::
  T_IsMonoidIsomorphism_438 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_2204 v0
  = coe d_isMonoidMonomorphism_446 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2206 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2206 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_412
            (coe d_isMonoidMonomorphism_446 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_2208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_2208 v7
du_isRelIsomorphism_2208 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_2208 v0
  = coe
      du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2210 v7
du_isRelMonomorphism_2210 ::
  T_IsMonoidIsomorphism_438 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2210 v0
  = let v1 = d_isMonoidMonomorphism_446 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.surjective
d_surjective_2212 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2212 v0 = coe d_surjective_448 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.ε-homo
d_ε'45'homo_2214 :: T_IsMonoidIsomorphism_438 -> AgdaAny
d_ε'45'homo_2214 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_412
         (coe d_isMonoidMonomorphism_446 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidIsomorphism.cong
d_cong_2216 ::
  T_IsMonoidIsomorphism_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2216 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_412
               (coe d_isMonoidMonomorphism_446 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.homo
d_homo_2220 ::
  T_IsMonoidMonomorphism_404 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2220 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.injective
d_injective_2222 ::
  T_IsMonoidMonomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2222 v0 = coe d_injective_414 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2224 ::
  T_IsMonoidMonomorphism_404 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2224 v0
  = coe
      d_isMagmaHomomorphism_388 (coe d_isMonoidHomomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isMagmaMonomorphism_2226
du_isMagmaMonomorphism_2226 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_2226 v0 v1
  = coe du_isMagmaMonomorphism_428 v1
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_2228 ::
  T_IsMonoidMonomorphism_404 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_2228 v0
  = coe d_isMonoidHomomorphism_412 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2230 ::
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2230 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe d_isMonoidHomomorphism_412 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2232 v7
du_isRelMonomorphism_2232 ::
  T_IsMonoidMonomorphism_404 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2232 v0
  = coe
      du_isRelMonomorphism_234 (coe du_isMagmaMonomorphism_428 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.ε-homo
d_ε'45'homo_2234 :: T_IsMonoidMonomorphism_404 -> AgdaAny
d_ε'45'homo_2234 v0
  = coe d_ε'45'homo_390 (coe d_isMonoidHomomorphism_412 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*.IsMonoidMonomorphism.cong
d_cong_2236 ::
  T_IsMonoidMonomorphism_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2236 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe d_isMonoidHomomorphism_412 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism
d_IsRingWithoutOneHomomorphism_2240 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism
d_IsRingWithoutOneIsoMorphism_2244 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism
d_IsRingWithoutOneMonomorphism_2248 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism.*-homo
d_'42''45'homo_2254 ::
  T_IsRingWithoutOneHomomorphism_1842 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2254 v0 = coe d_'42''45'homo_1852 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneHomomorphism_1842 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_2256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaHomomorphism_2256
du_'42''45'isMagmaHomomorphism_2256 ::
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneHomomorphism_1842 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_2256 v0 v1
  = coe du_'42''45'isMagmaHomomorphism_1872 v1
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism.homo
d_homo_2258 ::
  T_IsRingWithoutOneHomomorphism_1842 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_homo_2258 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe d_'43''45'isGroupHomomorphism_1850 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_2260 ::
  T_IsRingWithoutOneHomomorphism_1842 -> T_IsGroupHomomorphism_670
d_'43''45'isGroupHomomorphism_2260 v0
  = coe d_'43''45'isGroupHomomorphism_1850 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2262 ::
  T_IsRingWithoutOneHomomorphism_1842 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2262 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe d_'43''45'isGroupHomomorphism_1850 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_2264 ::
  T_IsRingWithoutOneHomomorphism_1842 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_2264 v0
  = coe
      d_isMonoidHomomorphism_678
      (coe d_'43''45'isGroupHomomorphism_1850 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism.ε-homo
d_ε'45'homo_2266 :: T_IsRingWithoutOneHomomorphism_1842 -> AgdaAny
d_ε'45'homo_2266 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe d_'43''45'isGroupHomomorphism_1850 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneHomomorphism_1842 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_2268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isNearSemiringHomomorphism_2268
du_isNearSemiringHomomorphism_2268 ::
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneHomomorphism_1842 ->
  T_IsNearSemiringHomomorphism_982
du_isNearSemiringHomomorphism_2268 v0 v1
  = coe du_isNearSemiringHomomorphism_1870 v1
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2270 ::
  T_IsRingWithoutOneHomomorphism_1842 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2270 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe d_'43''45'isGroupHomomorphism_1850 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism.⁻¹-homo
d_'8315''185''45'homo_2272 ::
  T_IsRingWithoutOneHomomorphism_1842 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_2272 v0
  = coe
      d_'8315''185''45'homo_680
      (coe d_'43''45'isGroupHomomorphism_1850 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneHomomorphism.cong
d_cong_2274 ::
  T_IsRingWithoutOneHomomorphism_1842 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2274 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe d_'43''45'isGroupHomomorphism_1850 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.*-homo
d_'42''45'homo_2278 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2278 v0
  = coe
      d_'42''45'homo_1852
      (coe
         d_isRingWithoutOneHomomorphism_1886
         (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_2280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2280 v7
du_'42''45'isMagmaHomomorphism_2280 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_2280 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1938 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_1872
         (coe d_isRingWithoutOneHomomorphism_1886 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_2282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaIsomorphism_240
d_'42''45'isMagmaIsomorphism_2282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaIsomorphism_2282
du_'42''45'isMagmaIsomorphism_2282 ::
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaIsomorphism_240
du_'42''45'isMagmaIsomorphism_2282 v0 v1
  = coe du_'42''45'isMagmaIsomorphism_1990 v1
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_2284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_2284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_2284 v7
du_'42''45'isMagmaMonomorphism_2284 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_2284 v0
  = coe
      du_'42''45'isMagmaMonomorphism_1924
      (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.homo
d_homo_2286 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2286 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_'43''45'isGroupHomomorphism_1850
               (coe
                  d_isRingWithoutOneHomomorphism_1886
                  (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_2288 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsGroupHomomorphism_670
d_'43''45'isGroupHomomorphism_2288 v0
  = coe
      d_'43''45'isGroupHomomorphism_1850
      (coe
         d_isRingWithoutOneHomomorphism_1886
         (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.+-isGroupIsomorphism
d_'43''45'isGroupIsomorphism_2290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsGroupIsomorphism_738
d_'43''45'isGroupIsomorphism_2290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'43''45'isGroupIsomorphism_2290
du_'43''45'isGroupIsomorphism_2290 ::
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsGroupIsomorphism_738
du_'43''45'isGroupIsomorphism_2290 v0 v1
  = coe du_'43''45'isGroupIsomorphism_1980 v1
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.+-isGroupMonomorphism
d_'43''45'isGroupMonomorphism_2292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsGroupMonomorphism_698
d_'43''45'isGroupMonomorphism_2292 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupMonomorphism_2292 v7
du_'43''45'isGroupMonomorphism_2292 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsGroupMonomorphism_698
du_'43''45'isGroupMonomorphism_2292 v0
  = coe
      du_'43''45'isGroupMonomorphism_1914
      (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2294 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2294 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_'43''45'isGroupHomomorphism_1850
            (coe
               d_isRingWithoutOneHomomorphism_1886
               (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isMagmaIsomorphism
d_isMagmaIsomorphism_2296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_2296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_2296 v7
du_isMagmaIsomorphism_2296 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_2296 v0
  = let v1 = coe du_'43''45'isGroupIsomorphism_1980 (coe v0) in
    coe
      (coe
         du_isMagmaIsomorphism_470
         (coe du_isMonoidIsomorphism_776 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_2298 v7
du_isMagmaMonomorphism_2298 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_2298 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1938 (coe v0) in
    coe
      (let v2 = coe du_'43''45'isGroupMonomorphism_1914 (coe v1) in
       coe
         (coe
            du_isMagmaMonomorphism_428
            (coe du_isMonoidMonomorphism_726 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_2300 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_2300 v0
  = coe
      d_isMonoidHomomorphism_678
      (coe
         d_'43''45'isGroupHomomorphism_1850
         (coe
            d_isRingWithoutOneHomomorphism_1886
            (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isMonoidIsomorphism
d_isMonoidIsomorphism_2302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMonoidIsomorphism_438
d_isMonoidIsomorphism_2302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidIsomorphism_2302 v7
du_isMonoidIsomorphism_2302 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMonoidIsomorphism_438
du_isMonoidIsomorphism_2302 v0
  = coe
      du_isMonoidIsomorphism_776
      (coe du_'43''45'isGroupIsomorphism_1980 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_2304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_2304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_2304 v7
du_isMonoidMonomorphism_2304 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> T_IsMonoidMonomorphism_404
du_isMonoidMonomorphism_2304 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1938 (coe v0) in
    coe
      (coe
         du_isMonoidMonomorphism_726
         (coe du_'43''45'isGroupMonomorphism_1914 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.ε-homo
d_ε'45'homo_2306 :: T_IsRingWithoutOneIsoMorphism_1930 -> AgdaAny
d_ε'45'homo_2306 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_'43''45'isGroupHomomorphism_1850
            (coe
               d_isRingWithoutOneHomomorphism_1886
               (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.injective
d_injective_2308 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2308 v0
  = coe
      d_injective_1888 (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_2310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringHomomorphism_2310 v7
du_isNearSemiringHomomorphism_2310 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  T_IsNearSemiringHomomorphism_982
du_isNearSemiringHomomorphism_2310 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1938 (coe v0) in
    coe
      (coe
         du_isNearSemiringHomomorphism_1870
         (coe d_isRingWithoutOneHomomorphism_1886 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isRelHomomorphism
d_isRelHomomorphism_2312 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2312 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_'43''45'isGroupHomomorphism_1850
               (coe
                  d_isRingWithoutOneHomomorphism_1886
                  (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isRelIsomorphism
d_isRelIsomorphism_2314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_2314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_2314 v7
du_isRelIsomorphism_2314 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_2314 v0
  = let v1 = coe du_'43''45'isGroupIsomorphism_1980 (coe v0) in
    coe
      (let v2 = coe du_isMonoidIsomorphism_776 (coe v1) in
       coe
         (coe
            du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isRelMonomorphism
d_isRelMonomorphism_2316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneIsoMorphism_1930 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2316 v7
du_isRelMonomorphism_2316 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2316 v0
  = let v1 = d_isRingWithoutOneMonomorphism_1938 (coe v0) in
    coe
      (let v2 = coe du_'43''45'isGroupMonomorphism_1914 (coe v1) in
       coe
         (let v3 = coe du_isMonoidMonomorphism_726 (coe v2) in
          coe
            (coe
               du_isRelMonomorphism_234
               (coe du_isMagmaMonomorphism_428 (coe v3)))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isRingWithoutOneHomomorphism
d_isRingWithoutOneHomomorphism_2318 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  T_IsRingWithoutOneHomomorphism_1842
d_isRingWithoutOneHomomorphism_2318 v0
  = coe
      d_isRingWithoutOneHomomorphism_1886
      (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.isRingWithoutOneMonomorphism
d_isRingWithoutOneMonomorphism_2320 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  T_IsRingWithoutOneMonomorphism_1878
d_isRingWithoutOneMonomorphism_2320 v0
  = coe d_isRingWithoutOneMonomorphism_1938 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.surjective
d_surjective_2322 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2322 v0 = coe d_surjective_1940 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.⁻¹-homo
d_'8315''185''45'homo_2324 ::
  T_IsRingWithoutOneIsoMorphism_1930 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_2324 v0
  = coe
      d_'8315''185''45'homo_680
      (coe
         d_'43''45'isGroupHomomorphism_1850
         (coe
            d_isRingWithoutOneHomomorphism_1886
            (coe d_isRingWithoutOneMonomorphism_1938 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneIsoMorphism.cong
d_cong_2326 ::
  T_IsRingWithoutOneIsoMorphism_1930 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2326 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe
                  d_'43''45'isGroupHomomorphism_1850
                  (coe
                     d_isRingWithoutOneHomomorphism_1886
                     (coe d_isRingWithoutOneMonomorphism_1938 (coe v0)))))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.*-homo
d_'42''45'homo_2330 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2330 v0
  = coe
      d_'42''45'homo_1852
      (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_2332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2332 v7
du_'42''45'isMagmaHomomorphism_2332 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_2332 v0
  = coe
      du_'42''45'isMagmaHomomorphism_1872
      (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_2334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_2334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMagmaMonomorphism_2334
du_'42''45'isMagmaMonomorphism_2334 ::
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_2334 v0 v1
  = coe du_'42''45'isMagmaMonomorphism_1924 v1
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.homo
d_homo_2336 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_homo_2336 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_'43''45'isGroupHomomorphism_1850
               (coe d_isRingWithoutOneHomomorphism_1886 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_2338 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsGroupHomomorphism_670
d_'43''45'isGroupHomomorphism_2338 v0
  = coe
      d_'43''45'isGroupHomomorphism_1850
      (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.+-isGroupMonomorphism
d_'43''45'isGroupMonomorphism_2340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsGroupMonomorphism_698
d_'43''45'isGroupMonomorphism_2340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'43''45'isGroupMonomorphism_2340
du_'43''45'isGroupMonomorphism_2340 ::
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsGroupMonomorphism_698
du_'43''45'isGroupMonomorphism_2340 v0 v1
  = coe du_'43''45'isGroupMonomorphism_1914 v1
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2342 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2342 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_'43''45'isGroupHomomorphism_1850
            (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_2344 v7
du_isMagmaMonomorphism_2344 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_2344 v0
  = let v1 = coe du_'43''45'isGroupMonomorphism_1914 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_428
         (coe du_isMonoidMonomorphism_726 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.isMonoidHomomorphism
d_isMonoidHomomorphism_2346 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMonoidHomomorphism_380
d_isMonoidHomomorphism_2346 v0
  = coe
      d_isMonoidHomomorphism_678
      (coe
         d_'43''45'isGroupHomomorphism_1850
         (coe d_isRingWithoutOneHomomorphism_1886 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.isMonoidMonomorphism
d_isMonoidMonomorphism_2348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_2348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_2348 v7
du_isMonoidMonomorphism_2348 ::
  T_IsRingWithoutOneMonomorphism_1878 -> T_IsMonoidMonomorphism_404
du_isMonoidMonomorphism_2348 v0
  = coe
      du_isMonoidMonomorphism_726
      (coe du_'43''45'isGroupMonomorphism_1914 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.ε-homo
d_ε'45'homo_2350 :: T_IsRingWithoutOneMonomorphism_1878 -> AgdaAny
d_ε'45'homo_2350 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_isMonoidHomomorphism_678
         (coe
            d_'43''45'isGroupHomomorphism_1850
            (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.injective
d_injective_2352 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2352 v0 = coe d_injective_1888 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_2354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringHomomorphism_2354 v7
du_isNearSemiringHomomorphism_2354 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  T_IsNearSemiringHomomorphism_982
du_isNearSemiringHomomorphism_2354 v0
  = coe
      du_isNearSemiringHomomorphism_1870
      (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2356 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2356 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_isMonoidHomomorphism_678
            (coe
               d_'43''45'isGroupHomomorphism_1850
               (coe d_isRingWithoutOneHomomorphism_1886 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingWithoutOneMonomorphism_1878 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2358 v7
du_isRelMonomorphism_2358 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2358 v0
  = let v1 = coe du_'43''45'isGroupMonomorphism_1914 (coe v0) in
    coe
      (let v2 = coe du_isMonoidMonomorphism_726 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_234
            (coe du_isMagmaMonomorphism_428 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.isRingWithoutOneHomomorphism
d_isRingWithoutOneHomomorphism_2360 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  T_IsRingWithoutOneHomomorphism_1842
d_isRingWithoutOneHomomorphism_2360 v0
  = coe d_isRingWithoutOneHomomorphism_1886 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.⁻¹-homo
d_'8315''185''45'homo_2362 ::
  T_IsRingWithoutOneMonomorphism_1878 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_2362 v0
  = coe
      d_'8315''185''45'homo_680
      (coe
         d_'43''45'isGroupHomomorphism_1850
         (coe d_isRingWithoutOneHomomorphism_1886 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.*+0.IsRingWithoutOneMonomorphism.cong
d_cong_2364 ::
  T_IsRingWithoutOneMonomorphism_1878 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2364 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_isMonoidHomomorphism_678
               (coe
                  d_'43''45'isGroupHomomorphism_1850
                  (coe d_isRingWithoutOneHomomorphism_1886 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms._.Homomorphic₁
d_Homomorphic'8321'_2370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_2370 = erased
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism
d_IsSemiringHomomorphism_2378 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism
d_IsSemiringIsomorphism_2382 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism
d_IsSemiringMonomorphism_2386 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.*-homo
d_'42''45'homo_2392 ::
  T_IsSemiringHomomorphism_1366 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2392 v0
  = coe
      d_'42''45'homo_992 (coe d_isNearSemiringHomomorphism_1374 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1366 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_2394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2394 v7
du_'42''45'isMagmaHomomorphism_2394 ::
  T_IsSemiringHomomorphism_1366 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_2394 v0
  = coe
      du_'42''45'isMagmaHomomorphism_1006
      (coe d_isNearSemiringHomomorphism_1374 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1366 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_2396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidHomomorphism_2396
du_'42''45'isMonoidHomomorphism_2396 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1366 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_2396 v0 v1
  = coe du_'42''45'isMonoidHomomorphism_1396 v1
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.homo
d_homo_2398 ::
  T_IsSemiringHomomorphism_1366 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2398 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1374 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2400 ::
  T_IsSemiringHomomorphism_1366 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2400 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1374 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2402 ::
  T_IsSemiringHomomorphism_1366 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_2402 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe d_isNearSemiringHomomorphism_1374 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.ε-homo
d_ε'45'homo_2404 :: T_IsSemiringHomomorphism_1366 -> AgdaAny
d_ε'45'homo_2404 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1374 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.1#-homo
d_1'35''45'homo_2406 :: T_IsSemiringHomomorphism_1366 -> AgdaAny
d_1'35''45'homo_2406 v0 = coe d_1'35''45'homo_1376 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2408 ::
  T_IsSemiringHomomorphism_1366 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_2408 v0
  = coe d_isNearSemiringHomomorphism_1374 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2410 ::
  T_IsSemiringHomomorphism_1366 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2410 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1374 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringHomomorphism.cong
d_cong_2412 ::
  T_IsSemiringHomomorphism_1366 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2412 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe d_isNearSemiringHomomorphism_1374 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-homo
d_'42''45'homo_2416 ::
  T_IsSemiringIsomorphism_1452 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2416 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_1410
            (coe d_isSemiringMonomorphism_1460 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_2418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2418 v7
du_'42''45'isMagmaHomomorphism_2418 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_2418 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (let v2 = d_isSemiringHomomorphism_1410 (coe v1) in
       coe
         (coe
            du_'42''45'isMagmaHomomorphism_1006
            (coe d_isNearSemiringHomomorphism_1374 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_2420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaIsomorphism_240
d_'42''45'isMagmaIsomorphism_2420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaIsomorphism_2420 v7
du_'42''45'isMagmaIsomorphism_2420 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaIsomorphism_240
du_'42''45'isMagmaIsomorphism_2420 v0
  = coe
      du_'42''45'isMagmaIsomorphism_1106
      (coe du_isNearSemiringIsomorphism_1500 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_2422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_2422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_2422 v7
du_'42''45'isMagmaMonomorphism_2422 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_2422 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaMonomorphism_1050
         (coe du_isNearSemiringMonomorphism_1438 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_2424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_2424 v7
du_'42''45'isMonoidHomomorphism_2424 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_2424 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoidHomomorphism_1396
         (coe d_isSemiringHomomorphism_1410 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMonoidIsomorphism
d_'42''45'isMonoidIsomorphism_2426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
d_'42''45'isMonoidIsomorphism_2426 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidIsomorphism_2426
du_'42''45'isMonoidIsomorphism_2426 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
du_'42''45'isMonoidIsomorphism_2426 v0 v1
  = coe du_'42''45'isMonoidIsomorphism_1508 v1
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_2428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
d_'42''45'isMonoidMonomorphism_2428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_2428 v7
du_'42''45'isMonoidMonomorphism_2428 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
du_'42''45'isMonoidMonomorphism_2428 v0
  = coe
      du_'42''45'isMonoidMonomorphism_1446
      (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.homo
d_homo_2430 ::
  T_IsSemiringIsomorphism_1452 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2430 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_1410
                  (coe d_isSemiringMonomorphism_1460 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2432 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2432 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_1410
               (coe d_isSemiringMonomorphism_1460 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2434 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_2434 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_1410
            (coe d_isSemiringMonomorphism_1460 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.+-isMonoidIsomorphism
d_'43''45'isMonoidIsomorphism_2436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
d_'43''45'isMonoidIsomorphism_2436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidIsomorphism_2436 v7
du_'43''45'isMonoidIsomorphism_2436 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
du_'43''45'isMonoidIsomorphism_2436 v0
  = coe
      du_'43''45'isMonoidIsomorphism_1098
      (coe du_isNearSemiringIsomorphism_1500 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_2438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_2438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_2438 v7
du_'43''45'isMonoidMonomorphism_2438 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_2438 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (coe
         du_'43''45'isMonoidMonomorphism_1042
         (coe du_isNearSemiringMonomorphism_1438 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.ε-homo
d_ε'45'homo_2440 :: T_IsSemiringIsomorphism_1452 -> AgdaAny
d_ε'45'homo_2440 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_1410
               (coe d_isSemiringMonomorphism_1460 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.1#-homo
d_1'35''45'homo_2442 :: T_IsSemiringIsomorphism_1452 -> AgdaAny
d_1'35''45'homo_2442 v0
  = coe
      d_1'35''45'homo_1376
      (coe
         d_isSemiringHomomorphism_1410
         (coe d_isSemiringMonomorphism_1460 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.injective
d_injective_2444 ::
  T_IsSemiringIsomorphism_1452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2444 v0
  = coe d_injective_1412 (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2446 ::
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_2446 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe
         d_isSemiringHomomorphism_1410
         (coe d_isSemiringMonomorphism_1460 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isNearSemiringIsomorphism
d_isNearSemiringIsomorphism_2448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringIsomorphism_1056
d_isNearSemiringIsomorphism_2448 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isNearSemiringIsomorphism_2448
du_isNearSemiringIsomorphism_2448 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringIsomorphism_1056
du_isNearSemiringIsomorphism_2448 v0 v1
  = coe du_isNearSemiringIsomorphism_1500 v1
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_2450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringMonomorphism_1012
d_isNearSemiringMonomorphism_2450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringMonomorphism_2450 v7
du_isNearSemiringMonomorphism_2450 ::
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringMonomorphism_1012
du_isNearSemiringMonomorphism_2450 v0
  = coe
      du_isNearSemiringMonomorphism_1438
      (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2452 ::
  T_IsSemiringIsomorphism_1452 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2452 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_1410
                  (coe d_isSemiringMonomorphism_1460 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_2454 ::
  T_IsSemiringIsomorphism_1452 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_2454 v0
  = coe
      d_isSemiringHomomorphism_1410
      (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.isSemiringMonomorphism
d_isSemiringMonomorphism_2456 ::
  T_IsSemiringIsomorphism_1452 -> T_IsSemiringMonomorphism_1402
d_isSemiringMonomorphism_2456 v0
  = coe d_isSemiringMonomorphism_1460 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.surjective
d_surjective_2458 ::
  T_IsSemiringIsomorphism_1452 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2458 v0 = coe d_surjective_1462 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringIsomorphism.cong
d_cong_2460 ::
  T_IsSemiringIsomorphism_1452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2460 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe
                     d_isSemiringHomomorphism_1410
                     (coe d_isSemiringMonomorphism_1460 (coe v0)))))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.*-homo
d_'42''45'homo_2464 ::
  T_IsSemiringMonomorphism_1402 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2464 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe d_isSemiringHomomorphism_1410 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_2466 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2466 v7
du_'42''45'isMagmaHomomorphism_2466 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_2466 v0
  = let v1 = d_isSemiringHomomorphism_1410 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_1006
         (coe d_isNearSemiringHomomorphism_1374 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_2468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_2468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_2468 v7
du_'42''45'isMagmaMonomorphism_2468 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_2468 v0
  = coe
      du_'42''45'isMagmaMonomorphism_1050
      (coe du_isNearSemiringMonomorphism_1438 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_2470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_2470 v7
du_'42''45'isMonoidHomomorphism_2470 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_2470 v0
  = coe
      du_'42''45'isMonoidHomomorphism_1396
      (coe d_isSemiringHomomorphism_1410 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_2472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
d_'42''45'isMonoidMonomorphism_2472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidMonomorphism_2472
du_'42''45'isMonoidMonomorphism_2472 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
du_'42''45'isMonoidMonomorphism_2472 v0 v1
  = coe du_'42''45'isMonoidMonomorphism_1446 v1
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.homo
d_homo_2474 ::
  T_IsSemiringMonomorphism_1402 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2474 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe d_isSemiringHomomorphism_1410 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2476 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2476 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_1410 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2478 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_2478 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe d_isSemiringHomomorphism_1410 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_2480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_2480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_2480 v7
du_'43''45'isMonoidMonomorphism_2480 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_2480 v0
  = coe
      du_'43''45'isMonoidMonomorphism_1042
      (coe du_isNearSemiringMonomorphism_1438 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.ε-homo
d_ε'45'homo_2482 :: T_IsSemiringMonomorphism_1402 -> AgdaAny
d_ε'45'homo_2482 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_1410 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.1#-homo
d_1'35''45'homo_2484 :: T_IsSemiringMonomorphism_1402 -> AgdaAny
d_1'35''45'homo_2484 v0
  = coe
      d_1'35''45'homo_1376 (coe d_isSemiringHomomorphism_1410 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.injective
d_injective_2486 ::
  T_IsSemiringMonomorphism_1402 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2486 v0 = coe d_injective_1412 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2488 ::
  T_IsSemiringMonomorphism_1402 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_2488 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe d_isSemiringHomomorphism_1410 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_2490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsNearSemiringMonomorphism_1012
d_isNearSemiringMonomorphism_2490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isNearSemiringMonomorphism_2490
du_isNearSemiringMonomorphism_2490 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsNearSemiringMonomorphism_1012
du_isNearSemiringMonomorphism_2490 v0 v1
  = coe du_isNearSemiringMonomorphism_1438 v1
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2492 ::
  T_IsSemiringMonomorphism_1402 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2492 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe d_isSemiringHomomorphism_1410 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_2494 ::
  T_IsSemiringMonomorphism_1402 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_2494 v0
  = coe d_isSemiringHomomorphism_1410 (coe v0)
-- Algebra.Morphism.Structures.RingMorphisms._.IsSemiringMonomorphism.cong
d_cong_2496 ::
  T_IsSemiringMonomorphism_1402 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2496 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe d_isSemiringHomomorphism_1410 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism
d_IsRingHomomorphism_2500 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingHomomorphism_2500
  = C_constructor_2540 T_IsSemiringHomomorphism_1366
                       (AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_2508 ::
  T_IsRingHomomorphism_2500 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_2508 v0
  = case coe v0 of
      C_constructor_2540 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism.-‿homo
d_'45''8255'homo_2510 ::
  T_IsRingHomomorphism_2500 -> AgdaAny -> AgdaAny
d_'45''8255'homo_2510 v0
  = case coe v0 of
      C_constructor_2540 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.*-homo
d_'42''45'homo_2514 ::
  T_IsRingHomomorphism_2500 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2514 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe d_isSemiringHomomorphism_2508 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingHomomorphism_2500 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_2516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2516 v7
du_'42''45'isMagmaHomomorphism_2516 ::
  T_IsRingHomomorphism_2500 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_2516 v0
  = let v1 = d_isSemiringHomomorphism_2508 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_1006
         (coe d_isNearSemiringHomomorphism_1374 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingHomomorphism_2500 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_2518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_2518 v7
du_'42''45'isMonoidHomomorphism_2518 ::
  T_IsRingHomomorphism_2500 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_2518 v0
  = coe
      du_'42''45'isMonoidHomomorphism_1396
      (coe d_isSemiringHomomorphism_2508 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.homo
d_homo_2520 ::
  T_IsRingHomomorphism_2500 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2520 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe d_isSemiringHomomorphism_2508 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_2522 ::
  T_IsRingHomomorphism_2500 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2522 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_2508 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2524 ::
  T_IsRingHomomorphism_2500 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_2524 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe d_isSemiringHomomorphism_2508 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.ε-homo
d_ε'45'homo_2526 :: T_IsRingHomomorphism_2500 -> AgdaAny
d_ε'45'homo_2526 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_2508 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.1#-homo
d_1'35''45'homo_2528 :: T_IsRingHomomorphism_2500 -> AgdaAny
d_1'35''45'homo_2528 v0
  = coe
      d_1'35''45'homo_1376 (coe d_isSemiringHomomorphism_2508 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2530 ::
  T_IsRingHomomorphism_2500 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_2530 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe d_isSemiringHomomorphism_2508 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_2532 ::
  T_IsRingHomomorphism_2500 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2532 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe d_isSemiringHomomorphism_2508 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism._.cong
d_cong_2534 ::
  T_IsRingHomomorphism_2500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2534 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe d_isSemiringHomomorphism_2508 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_2536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingHomomorphism_2500 -> T_IsGroupHomomorphism_670
d_'43''45'isGroupHomomorphism_2536 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupHomomorphism_2536 v7
du_'43''45'isGroupHomomorphism_2536 ::
  T_IsRingHomomorphism_2500 -> T_IsGroupHomomorphism_670
du_'43''45'isGroupHomomorphism_2536 v0
  = coe
      C_constructor_694
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_2508 (coe v0))))
      (coe d_'45''8255'homo_2510 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingHomomorphism.isRingWithoutOneHomomorphism
d_isRingWithoutOneHomomorphism_2538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingHomomorphism_2500 -> T_IsRingWithoutOneHomomorphism_1842
d_isRingWithoutOneHomomorphism_2538 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRingWithoutOneHomomorphism_2538 v7
du_isRingWithoutOneHomomorphism_2538 ::
  T_IsRingHomomorphism_2500 -> T_IsRingWithoutOneHomomorphism_1842
du_isRingWithoutOneHomomorphism_2538 v0
  = coe
      C_constructor_1874
      (coe du_'43''45'isGroupHomomorphism_2536 (coe v0))
      (coe
         d_'42''45'homo_992
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_2508 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism
d_IsRingMonomorphism_2544 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingMonomorphism_2544
  = C_constructor_2606 T_IsRingHomomorphism_2500
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism.isRingHomomorphism
d_isRingHomomorphism_2552 ::
  T_IsRingMonomorphism_2544 -> T_IsRingHomomorphism_2500
d_isRingHomomorphism_2552 v0
  = case coe v0 of
      C_constructor_2606 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism.injective
d_injective_2554 ::
  T_IsRingMonomorphism_2544 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2554 v0
  = case coe v0 of
      C_constructor_2606 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.*-homo
d_'42''45'homo_2558 ::
  T_IsRingMonomorphism_2544 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2558 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_2508
            (coe d_isRingHomomorphism_2552 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2544 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_2560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2560 v7
du_'42''45'isMagmaHomomorphism_2560 ::
  T_IsRingMonomorphism_2544 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_2560 v0
  = let v1 = d_isRingHomomorphism_2552 (coe v0) in
    coe
      (let v2 = d_isSemiringHomomorphism_2508 (coe v1) in
       coe
         (coe
            du_'42''45'isMagmaHomomorphism_1006
            (coe d_isNearSemiringHomomorphism_1374 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2544 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_2562 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_2562 v7
du_'42''45'isMonoidHomomorphism_2562 ::
  T_IsRingMonomorphism_2544 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_2562 v0
  = let v1 = d_isRingHomomorphism_2552 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoidHomomorphism_1396
         (coe d_isSemiringHomomorphism_2508 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.homo
d_homo_2564 ::
  T_IsRingMonomorphism_2544 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2564 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_2508
                  (coe d_isRingHomomorphism_2552 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_2566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2544 -> T_IsGroupHomomorphism_670
d_'43''45'isGroupHomomorphism_2566 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupHomomorphism_2566 v7
du_'43''45'isGroupHomomorphism_2566 ::
  T_IsRingMonomorphism_2544 -> T_IsGroupHomomorphism_670
du_'43''45'isGroupHomomorphism_2566 v0
  = coe
      du_'43''45'isGroupHomomorphism_2536
      (coe d_isRingHomomorphism_2552 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_2568 ::
  T_IsRingMonomorphism_2544 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2568 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_2508
               (coe d_isRingHomomorphism_2552 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2570 ::
  T_IsRingMonomorphism_2544 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_2570 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_2508
            (coe d_isRingHomomorphism_2552 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.-‿homo
d_'45''8255'homo_2572 ::
  T_IsRingMonomorphism_2544 -> AgdaAny -> AgdaAny
d_'45''8255'homo_2572 v0
  = coe
      d_'45''8255'homo_2510 (coe d_isRingHomomorphism_2552 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.ε-homo
d_ε'45'homo_2574 :: T_IsRingMonomorphism_2544 -> AgdaAny
d_ε'45'homo_2574 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_2508
               (coe d_isRingHomomorphism_2552 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.1#-homo
d_1'35''45'homo_2576 :: T_IsRingMonomorphism_2544 -> AgdaAny
d_1'35''45'homo_2576 v0
  = coe
      d_1'35''45'homo_1376
      (coe
         d_isSemiringHomomorphism_2508
         (coe d_isRingHomomorphism_2552 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2578 ::
  T_IsRingMonomorphism_2544 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_2578 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe
         d_isSemiringHomomorphism_2508
         (coe d_isRingHomomorphism_2552 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_2580 ::
  T_IsRingMonomorphism_2544 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2580 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_2508
                  (coe d_isRingHomomorphism_2552 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isRingWithoutOneHomomorphism
d_isRingWithoutOneHomomorphism_2582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2544 -> T_IsRingWithoutOneHomomorphism_1842
d_isRingWithoutOneHomomorphism_2582 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRingWithoutOneHomomorphism_2582 v7
du_isRingWithoutOneHomomorphism_2582 ::
  T_IsRingMonomorphism_2544 -> T_IsRingWithoutOneHomomorphism_1842
du_isRingWithoutOneHomomorphism_2582 v0
  = coe
      du_isRingWithoutOneHomomorphism_2538
      (coe d_isRingHomomorphism_2552 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isSemiringHomomorphism
d_isSemiringHomomorphism_2584 ::
  T_IsRingMonomorphism_2544 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_2584 v0
  = coe
      d_isSemiringHomomorphism_2508
      (coe d_isRingHomomorphism_2552 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.cong
d_cong_2586 ::
  T_IsRingMonomorphism_2544 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2586 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe
                     d_isSemiringHomomorphism_2508
                     (coe d_isRingHomomorphism_2552 (coe v0)))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism.isSemiringMonomorphism
d_isSemiringMonomorphism_2588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2544 -> T_IsSemiringMonomorphism_1402
d_isSemiringMonomorphism_2588 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isSemiringMonomorphism_2588 v7
du_isSemiringMonomorphism_2588 ::
  T_IsRingMonomorphism_2544 -> T_IsSemiringMonomorphism_1402
du_isSemiringMonomorphism_2588 v0
  = coe
      C_constructor_1448
      (coe
         d_isSemiringHomomorphism_2508
         (coe d_isRingHomomorphism_2552 (coe v0)))
      (coe d_injective_2554 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism.+-isGroupMonomorphism
d_'43''45'isGroupMonomorphism_2590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2544 -> T_IsGroupMonomorphism_698
d_'43''45'isGroupMonomorphism_2590 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupMonomorphism_2590 v7
du_'43''45'isGroupMonomorphism_2590 ::
  T_IsRingMonomorphism_2544 -> T_IsGroupMonomorphism_698
du_'43''45'isGroupMonomorphism_2590 v0
  = coe
      C_constructor_734
      (coe
         du_'43''45'isGroupHomomorphism_2536
         (coe d_isRingHomomorphism_2552 (coe v0)))
      (coe d_injective_2554 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_2594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2544 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2594 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_2594 v7
du_isMagmaMonomorphism_2594 ::
  T_IsRingMonomorphism_2544 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_2594 v0
  = let v1 = coe du_'43''45'isGroupMonomorphism_2590 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_428
         (coe du_isMonoidMonomorphism_726 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isMonoidMonomorphism
d_isMonoidMonomorphism_2596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2544 -> T_IsMonoidMonomorphism_404
d_isMonoidMonomorphism_2596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidMonomorphism_2596 v7
du_isMonoidMonomorphism_2596 ::
  T_IsRingMonomorphism_2544 -> T_IsMonoidMonomorphism_404
du_isMonoidMonomorphism_2596 v0
  = coe
      du_isMonoidMonomorphism_726
      (coe du_'43''45'isGroupMonomorphism_2590 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_2598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2544 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2598 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2598 v7
du_isRelMonomorphism_2598 ::
  T_IsRingMonomorphism_2544 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2598 v0
  = let v1 = coe du_'43''45'isGroupMonomorphism_2590 (coe v0) in
    coe
      (let v2 = coe du_isMonoidMonomorphism_726 (coe v1) in
       coe
         (coe
            du_isRelMonomorphism_234
            (coe du_isMagmaMonomorphism_428 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_2600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2544 -> T_IsMonoidMonomorphism_404
d_'42''45'isMonoidMonomorphism_2600 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_2600 v7
du_'42''45'isMonoidMonomorphism_2600 ::
  T_IsRingMonomorphism_2544 -> T_IsMonoidMonomorphism_404
du_'42''45'isMonoidMonomorphism_2600 v0
  = coe
      C_constructor_434
      (coe
         du_'42''45'isMonoidHomomorphism_1396
         (coe
            d_isSemiringHomomorphism_2508
            (coe d_isRingHomomorphism_2552 (coe v0))))
      (coe d_injective_2554 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingMonomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_2604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingMonomorphism_2544 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2604 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_2604 v7
du_isMagmaMonomorphism_2604 ::
  T_IsRingMonomorphism_2544 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_2604 v0
  = coe
      du_isMagmaMonomorphism_428
      (coe du_'42''45'isMonoidMonomorphism_2600 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism
d_IsRingIsomorphism_2610 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingIsomorphism_2610
  = C_constructor_2684 T_IsRingMonomorphism_2544
                       (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism.isRingMonomorphism
d_isRingMonomorphism_2618 ::
  T_IsRingIsomorphism_2610 -> T_IsRingMonomorphism_2544
d_isRingMonomorphism_2618 v0
  = case coe v0 of
      C_constructor_2684 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism.surjective
d_surjective_2620 ::
  T_IsRingIsomorphism_2610 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2620 v0
  = case coe v0 of
      C_constructor_2684 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.*-homo
d_'42''45'homo_2624 ::
  T_IsRingIsomorphism_2610 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_2624 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_2508
            (coe
               d_isRingHomomorphism_2552
               (coe d_isRingMonomorphism_2618 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_2626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_2626 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_2626 v7
du_'42''45'isMagmaHomomorphism_2626 ::
  T_IsRingIsomorphism_2610 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_2626 v0
  = let v1 = d_isRingMonomorphism_2618 (coe v0) in
    coe
      (let v2 = d_isRingHomomorphism_2552 (coe v1) in
       coe
         (let v3 = d_isSemiringHomomorphism_2508 (coe v2) in
          coe
            (coe
               du_'42''45'isMagmaHomomorphism_1006
               (coe d_isNearSemiringHomomorphism_1374 (coe v3)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isMagmaMonomorphism
d_isMagmaMonomorphism_2628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2628 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaMonomorphism_2628 v7
du_isMagmaMonomorphism_2628 ::
  T_IsRingIsomorphism_2610 -> T_IsMagmaMonomorphism_214
du_isMagmaMonomorphism_2628 v0
  = let v1 = d_isRingMonomorphism_2618 (coe v0) in
    coe
      (coe
         du_isMagmaMonomorphism_428
         (coe du_'42''45'isMonoidMonomorphism_2600 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_2630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_2630 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_2630 v7
du_'42''45'isMonoidHomomorphism_2630 ::
  T_IsRingIsomorphism_2610 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_2630 v0
  = let v1 = d_isRingMonomorphism_2618 (coe v0) in
    coe
      (let v2 = d_isRingHomomorphism_2552 (coe v1) in
       coe
         (coe
            du_'42''45'isMonoidHomomorphism_1396
            (coe d_isSemiringHomomorphism_2508 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_2632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsMonoidMonomorphism_404
d_'42''45'isMonoidMonomorphism_2632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_2632 v7
du_'42''45'isMonoidMonomorphism_2632 ::
  T_IsRingIsomorphism_2610 -> T_IsMonoidMonomorphism_404
du_'42''45'isMonoidMonomorphism_2632 v0
  = coe
      du_'42''45'isMonoidMonomorphism_2600
      (coe d_isRingMonomorphism_2618 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.homo
d_homo_2634 ::
  T_IsRingIsomorphism_2610 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2634 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_2508
                  (coe
                     d_isRingHomomorphism_2552
                     (coe d_isRingMonomorphism_2618 (coe v0)))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.+-isGroupHomomorphism
d_'43''45'isGroupHomomorphism_2636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsGroupHomomorphism_670
d_'43''45'isGroupHomomorphism_2636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupHomomorphism_2636 v7
du_'43''45'isGroupHomomorphism_2636 ::
  T_IsRingIsomorphism_2610 -> T_IsGroupHomomorphism_670
du_'43''45'isGroupHomomorphism_2636 v0
  = let v1 = d_isRingMonomorphism_2618 (coe v0) in
    coe
      (coe
         du_'43''45'isGroupHomomorphism_2536
         (coe d_isRingHomomorphism_2552 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.+-isGroupMonomorphism
d_'43''45'isGroupMonomorphism_2638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsGroupMonomorphism_698
d_'43''45'isGroupMonomorphism_2638 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupMonomorphism_2638 v7
du_'43''45'isGroupMonomorphism_2638 ::
  T_IsRingIsomorphism_2610 -> T_IsGroupMonomorphism_698
du_'43''45'isGroupMonomorphism_2638 v0
  = coe
      du_'43''45'isGroupMonomorphism_2590
      (coe d_isRingMonomorphism_2618 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_2640 ::
  T_IsRingIsomorphism_2610 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2640 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_2508
               (coe
                  d_isRingHomomorphism_2552
                  (coe d_isRingMonomorphism_2618 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_2642 ::
  T_IsRingIsomorphism_2610 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_2642 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_2508
            (coe
               d_isRingHomomorphism_2552
               (coe d_isRingMonomorphism_2618 (coe v0)))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.-‿homo
d_'45''8255'homo_2644 ::
  T_IsRingIsomorphism_2610 -> AgdaAny -> AgdaAny
d_'45''8255'homo_2644 v0
  = coe
      d_'45''8255'homo_2510
      (coe
         d_isRingHomomorphism_2552 (coe d_isRingMonomorphism_2618 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.ε-homo
d_ε'45'homo_2646 :: T_IsRingIsomorphism_2610 -> AgdaAny
d_ε'45'homo_2646 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_2508
               (coe
                  d_isRingHomomorphism_2552
                  (coe d_isRingMonomorphism_2618 (coe v0))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.1#-homo
d_1'35''45'homo_2648 :: T_IsRingIsomorphism_2610 -> AgdaAny
d_1'35''45'homo_2648 v0
  = coe
      d_1'35''45'homo_1376
      (coe
         d_isSemiringHomomorphism_2508
         (coe
            d_isRingHomomorphism_2552
            (coe d_isRingMonomorphism_2618 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.injective
d_injective_2650 ::
  T_IsRingIsomorphism_2610 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2650 v0
  = coe d_injective_2554 (coe d_isRingMonomorphism_2618 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_2652 ::
  T_IsRingIsomorphism_2610 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_2652 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe
         d_isSemiringHomomorphism_2508
         (coe
            d_isRingHomomorphism_2552
            (coe d_isRingMonomorphism_2618 (coe v0))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_2654 ::
  T_IsRingIsomorphism_2610 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2654 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_2508
                  (coe
                     d_isRingHomomorphism_2552
                     (coe d_isRingMonomorphism_2618 (coe v0)))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isRingHomomorphism
d_isRingHomomorphism_2656 ::
  T_IsRingIsomorphism_2610 -> T_IsRingHomomorphism_2500
d_isRingHomomorphism_2656 v0
  = coe
      d_isRingHomomorphism_2552 (coe d_isRingMonomorphism_2618 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isRingWithoutOneHomomorphism
d_isRingWithoutOneHomomorphism_2658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsRingWithoutOneHomomorphism_1842
d_isRingWithoutOneHomomorphism_2658 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRingWithoutOneHomomorphism_2658 v7
du_isRingWithoutOneHomomorphism_2658 ::
  T_IsRingIsomorphism_2610 -> T_IsRingWithoutOneHomomorphism_1842
du_isRingWithoutOneHomomorphism_2658 v0
  = let v1 = d_isRingMonomorphism_2618 (coe v0) in
    coe
      (coe
         du_isRingWithoutOneHomomorphism_2538
         (coe d_isRingHomomorphism_2552 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isSemiringHomomorphism
d_isSemiringHomomorphism_2660 ::
  T_IsRingIsomorphism_2610 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_2660 v0
  = coe
      d_isSemiringHomomorphism_2508
      (coe
         d_isRingHomomorphism_2552 (coe d_isRingMonomorphism_2618 (coe v0)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isSemiringMonomorphism
d_isSemiringMonomorphism_2662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsSemiringMonomorphism_1402
d_isSemiringMonomorphism_2662 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isSemiringMonomorphism_2662 v7
du_isSemiringMonomorphism_2662 ::
  T_IsRingIsomorphism_2610 -> T_IsSemiringMonomorphism_1402
du_isSemiringMonomorphism_2662 v0
  = coe
      du_isSemiringMonomorphism_2588
      (coe d_isRingMonomorphism_2618 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.cong
d_cong_2664 ::
  T_IsRingIsomorphism_2610 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2664 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe
                     d_isSemiringHomomorphism_2508
                     (coe
                        d_isRingHomomorphism_2552
                        (coe d_isRingMonomorphism_2618 (coe v0))))))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism.isSemiringIsomorphism
d_isSemiringIsomorphism_2666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsSemiringIsomorphism_1452
d_isSemiringIsomorphism_2666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isSemiringIsomorphism_2666 v7
du_isSemiringIsomorphism_2666 ::
  T_IsRingIsomorphism_2610 -> T_IsSemiringIsomorphism_1452
du_isSemiringIsomorphism_2666 v0
  = coe
      C_constructor_1510
      (coe
         du_isSemiringMonomorphism_2588
         (coe d_isRingMonomorphism_2618 (coe v0)))
      (coe d_surjective_2620 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism.+-isGroupIsomorphism
d_'43''45'isGroupIsomorphism_2668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsGroupIsomorphism_738
d_'43''45'isGroupIsomorphism_2668 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isGroupIsomorphism_2668 v7
du_'43''45'isGroupIsomorphism_2668 ::
  T_IsRingIsomorphism_2610 -> T_IsGroupIsomorphism_738
du_'43''45'isGroupIsomorphism_2668 v0
  = coe
      C_constructor_784
      (coe
         du_'43''45'isGroupMonomorphism_2590
         (coe d_isRingMonomorphism_2618 (coe v0)))
      (coe d_surjective_2620 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isMagmaIsomorphism
d_isMagmaIsomorphism_2672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_2672 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_2672 v7
du_isMagmaIsomorphism_2672 ::
  T_IsRingIsomorphism_2610 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_2672 v0
  = let v1 = coe du_'43''45'isGroupIsomorphism_2668 (coe v0) in
    coe
      (coe
         du_isMagmaIsomorphism_470
         (coe du_isMonoidIsomorphism_776 (coe v1)))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isMonoidIsomorphism
d_isMonoidIsomorphism_2674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsMonoidIsomorphism_438
d_isMonoidIsomorphism_2674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMonoidIsomorphism_2674 v7
du_isMonoidIsomorphism_2674 ::
  T_IsRingIsomorphism_2610 -> T_IsMonoidIsomorphism_438
du_isMonoidIsomorphism_2674 v0
  = coe
      du_isMonoidIsomorphism_776
      (coe du_'43''45'isGroupIsomorphism_2668 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isRelIsomorphism
d_isRelIsomorphism_2676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_2676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_2676 v7
du_isRelIsomorphism_2676 ::
  T_IsRingIsomorphism_2610 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_2676 v0
  = let v1 = coe du_'43''45'isGroupIsomorphism_2668 (coe v0) in
    coe
      (let v2 = coe du_isMonoidIsomorphism_776 (coe v1) in
       coe
         (coe
            du_isRelIsomorphism_266 (coe du_isMagmaIsomorphism_470 (coe v2))))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism.*-isMonoidIsomorphism
d_'42''45'isMonoidIsomorphism_2678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsMonoidIsomorphism_438
d_'42''45'isMonoidIsomorphism_2678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidIsomorphism_2678 v7
du_'42''45'isMonoidIsomorphism_2678 ::
  T_IsRingIsomorphism_2610 -> T_IsMonoidIsomorphism_438
du_'42''45'isMonoidIsomorphism_2678 v0
  = coe
      C_constructor_476
      (coe
         du_'42''45'isMonoidMonomorphism_2600
         (coe d_isRingMonomorphism_2618 (coe v0)))
      (coe d_surjective_2620 (coe v0))
-- Algebra.Morphism.Structures.RingMorphisms.IsRingIsomorphism._.isMagmaIsomorphism
d_isMagmaIsomorphism_2682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290 ->
  (AgdaAny -> AgdaAny) ->
  T_IsRingIsomorphism_2610 -> T_IsMagmaIsomorphism_240
d_isMagmaIsomorphism_2682 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isMagmaIsomorphism_2682 v7
du_isMagmaIsomorphism_2682 ::
  T_IsRingIsomorphism_2610 -> T_IsMagmaIsomorphism_240
du_isMagmaIsomorphism_2682 v0
  = coe
      du_isMagmaIsomorphism_470
      (coe du_'42''45'isMonoidIsomorphism_2678 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms._._//_
d__'47''47'__2702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__2702 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'47''47'__2702 v4
du__'47''47'__2702 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__2702 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'47''47'__374 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms._._\\_
d__'92''92'__2704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'92''92'__2704 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'92''92'__2704 v4
du__'92''92'__2704 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'92''92'__2704 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'92''92'__372 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms._._∙_
d__'8729'__2706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__2706 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8729'__2706 v4
du__'8729'__2706 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8729'__2706 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__370 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms._._≈_
d__'8776'__2708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__2708 = erased
-- Algebra.Morphism.Structures.QuasigroupMorphisms._.Carrier
d_Carrier_2714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 -> ()
d_Carrier_2714 = erased
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaHomomorphism
d_IsMagmaHomomorphism_2742 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism
d_IsMagmaIsomorphism_2746 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism
d_IsMagmaMonomorphism_2750 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaHomomorphism.homo
d_homo_2756 ::
  T_IsMagmaHomomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2756 v0 = coe d_homo_204 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2758 ::
  T_IsMagmaHomomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2758 v0 = coe d_isRelHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaHomomorphism.cong
d_cong_2760 ::
  T_IsMagmaHomomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2760 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.homo
d_homo_2764 ::
  T_IsMagmaIsomorphism_240 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2764 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.injective
d_injective_2766 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2766 v0
  = coe d_injective_224 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2768 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2768 v0
  = coe
      d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2770 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2770 v0
  = coe d_isMagmaMonomorphism_248 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2772 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2772 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_2774 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_2774
du_isRelIsomorphism_2774 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_2774 v0 v1 = coe du_isRelIsomorphism_266 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2776 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2776 v7
du_isRelMonomorphism_2776 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2776 v0
  = coe
      du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.surjective
d_surjective_2778 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2778 v0 = coe d_surjective_250 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaIsomorphism.cong
d_cong_2780 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2780 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_222
            (coe d_isMagmaMonomorphism_248 (coe v0))))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.homo
d_homo_2784 ::
  T_IsMagmaMonomorphism_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2784 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.injective
d_injective_2786 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2786 v0 = coe d_injective_224 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2788 ::
  T_IsMagmaMonomorphism_214 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2788 v0
  = coe d_isMagmaHomomorphism_222 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2790 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2790 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2792 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_2792
du_isRelMonomorphism_2792 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2792 v0 v1 = coe du_isRelMonomorphism_234 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.∙.IsMagmaMonomorphism.cong
d_cong_2794 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2794 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaHomomorphism
d_IsMagmaHomomorphism_2798 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism
d_IsMagmaIsomorphism_2802 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism
d_IsMagmaMonomorphism_2806 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaHomomorphism.homo
d_homo_2812 ::
  T_IsMagmaHomomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2812 v0 = coe d_homo_204 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2814 ::
  T_IsMagmaHomomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2814 v0 = coe d_isRelHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaHomomorphism.cong
d_cong_2816 ::
  T_IsMagmaHomomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2816 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.homo
d_homo_2820 ::
  T_IsMagmaIsomorphism_240 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2820 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.injective
d_injective_2822 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2822 v0
  = coe d_injective_224 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2824 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2824 v0
  = coe
      d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2826 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2826 v0
  = coe d_isMagmaMonomorphism_248 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2828 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2828 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_2830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_2830
du_isRelIsomorphism_2830 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_2830 v0 v1 = coe du_isRelIsomorphism_266 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2832 v7
du_isRelMonomorphism_2832 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2832 v0
  = coe
      du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.surjective
d_surjective_2834 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2834 v0 = coe d_surjective_250 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaIsomorphism.cong
d_cong_2836 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2836 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_222
            (coe d_isMagmaMonomorphism_248 (coe v0))))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.homo
d_homo_2840 ::
  T_IsMagmaMonomorphism_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2840 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.injective
d_injective_2842 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2842 v0 = coe d_injective_224 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2844 ::
  T_IsMagmaMonomorphism_214 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2844 v0
  = coe d_isMagmaHomomorphism_222 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2846 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2846 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2848 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_2848
du_isRelMonomorphism_2848 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2848 v0 v1 = coe du_isRelMonomorphism_234 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.\\.IsMagmaMonomorphism.cong
d_cong_2850 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2850 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaHomomorphism
d_IsMagmaHomomorphism_2854 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism
d_IsMagmaIsomorphism_2858 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism
d_IsMagmaMonomorphism_2862 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaHomomorphism.homo
d_homo_2868 ::
  T_IsMagmaHomomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2868 v0 = coe d_homo_204 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2870 ::
  T_IsMagmaHomomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2870 v0 = coe d_isRelHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaHomomorphism.cong
d_cong_2872 ::
  T_IsMagmaHomomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2872 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.homo
d_homo_2876 ::
  T_IsMagmaIsomorphism_240 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2876 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.injective
d_injective_2878 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2878 v0
  = coe d_injective_224 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2880 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2880 v0
  = coe
      d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_2882 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_2882 v0
  = coe d_isMagmaMonomorphism_248 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_2884 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2884 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_2886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_2886 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_2886
du_isRelIsomorphism_2886 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_2886 v0 v1 = coe du_isRelIsomorphism_266 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_2888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2888 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2888 v7
du_isRelMonomorphism_2888 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2888 v0
  = coe
      du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.surjective
d_surjective_2890 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_2890 v0 = coe d_surjective_250 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaIsomorphism.cong
d_cong_2892 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2892 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_222
            (coe d_isMagmaMonomorphism_248 (coe v0))))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.homo
d_homo_2896 ::
  T_IsMagmaMonomorphism_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_2896 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.injective
d_injective_2898 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2898 v0 = coe d_injective_224 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_2900 ::
  T_IsMagmaMonomorphism_214 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_2900 v0
  = coe d_isMagmaHomomorphism_222 (coe v0)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_2902 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2902 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_2904 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2904 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_2904
du_isRelMonomorphism_2904 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2904 v0 v1 = coe du_isRelMonomorphism_234 v1
-- Algebra.Morphism.Structures.QuasigroupMorphisms.//.IsMagmaMonomorphism.cong
d_cong_2906 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2906 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms._.Homomorphic₂
d_Homomorphic'8322'_2914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_2914 = erased
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism
d_IsQuasigroupHomomorphism_2920 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsQuasigroupHomomorphism_2920
  = C_constructor_2950 MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
                       (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.isRelHomomorphism
d_isRelHomomorphism_2932 ::
  T_IsQuasigroupHomomorphism_2920 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2932 v0
  = case coe v0 of
      C_constructor_2950 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.∙-homo
d_'8729''45'homo_2934 ::
  T_IsQuasigroupHomomorphism_2920 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_2934 v0
  = case coe v0 of
      C_constructor_2950 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.\\-homo
d_'92''92''45'homo_2936 ::
  T_IsQuasigroupHomomorphism_2920 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_2936 v0
  = case coe v0 of
      C_constructor_2950 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.//-homo
d_'47''47''45'homo_2938 ::
  T_IsQuasigroupHomomorphism_2920 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_2938 v0
  = case coe v0 of
      C_constructor_2950 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism._.cong
d_cong_2942 ::
  T_IsQuasigroupHomomorphism_2920 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2942 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_2932 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_2944 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
d_'8729''45'isMagmaHomomorphism_2944 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_2944 v7
du_'8729''45'isMagmaHomomorphism_2944 ::
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
du_'8729''45'isMagmaHomomorphism_2944 v0
  = coe
      C_constructor_210 (coe d_isRelHomomorphism_2932 (coe v0))
      (coe d_'8729''45'homo_2934 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_2946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
d_'92''92''45'isMagmaHomomorphism_2946 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_2946 v7
du_'92''92''45'isMagmaHomomorphism_2946 ::
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
du_'92''92''45'isMagmaHomomorphism_2946 v0
  = coe
      C_constructor_210 (coe d_isRelHomomorphism_2932 (coe v0))
      (coe d_'92''92''45'homo_2936 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupHomomorphism.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_2948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
d_'47''47''45'isMagmaHomomorphism_2948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_2948 v7
du_'47''47''45'isMagmaHomomorphism_2948 ::
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
du_'47''47''45'isMagmaHomomorphism_2948 v0
  = coe
      C_constructor_210 (coe d_isRelHomomorphism_2932 (coe v0))
      (coe d_'47''47''45'homo_2938 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism
d_IsQuasigroupMonomorphism_2954 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsQuasigroupMonomorphism_2954
  = C_constructor_2994 T_IsQuasigroupHomomorphism_2920
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_2962 ::
  T_IsQuasigroupMonomorphism_2954 -> T_IsQuasigroupHomomorphism_2920
d_isQuasigroupHomomorphism_2962 v0
  = case coe v0 of
      C_constructor_2994 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism.injective
d_injective_2964 ::
  T_IsQuasigroupMonomorphism_2954 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_2964 v0
  = case coe v0 of
      C_constructor_2994 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.//-homo
d_'47''47''45'homo_2968 ::
  T_IsQuasigroupMonomorphism_2954 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_2968 v0
  = coe
      d_'47''47''45'homo_2938
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_2970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
d_'47''47''45'isMagmaHomomorphism_2970 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_2970 v7
du_'47''47''45'isMagmaHomomorphism_2970 ::
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
du_'47''47''45'isMagmaHomomorphism_2970 v0
  = coe
      du_'47''47''45'isMagmaHomomorphism_2948
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.\\-homo
d_'92''92''45'homo_2972 ::
  T_IsQuasigroupMonomorphism_2954 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_2972 v0
  = coe
      d_'92''92''45'homo_2936
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_2974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
d_'92''92''45'isMagmaHomomorphism_2974 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_2974 v7
du_'92''92''45'isMagmaHomomorphism_2974 ::
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
du_'92''92''45'isMagmaHomomorphism_2974 v0
  = coe
      du_'92''92''45'isMagmaHomomorphism_2946
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_2976 ::
  T_IsQuasigroupMonomorphism_2954 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_2976 v0
  = coe
      d_isRelHomomorphism_2932
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.∙-homo
d_'8729''45'homo_2978 ::
  T_IsQuasigroupMonomorphism_2954 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_2978 v0
  = coe
      d_'8729''45'homo_2934
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_2980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
d_'8729''45'isMagmaHomomorphism_2980 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_2980 v7
du_'8729''45'isMagmaHomomorphism_2980 ::
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
du_'8729''45'isMagmaHomomorphism_2980 v0
  = coe
      du_'8729''45'isMagmaHomomorphism_2944
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.cong
d_cong_2982 ::
  T_IsQuasigroupMonomorphism_2954 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_2982 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2932
         (coe d_isQuasigroupHomomorphism_2962 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism.∙-isMagmaMonomorphism
d_'8729''45'isMagmaMonomorphism_2984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
d_'8729''45'isMagmaMonomorphism_2984 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaMonomorphism_2984 v7
du_'8729''45'isMagmaMonomorphism_2984 ::
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
du_'8729''45'isMagmaMonomorphism_2984 v0
  = coe
      C_constructor_236
      (coe
         du_'8729''45'isMagmaHomomorphism_2944
         (coe d_isQuasigroupHomomorphism_2962 (coe v0)))
      (coe d_injective_2964 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism.\\-isMagmaMonomorphism
d_'92''92''45'isMagmaMonomorphism_2986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
d_'92''92''45'isMagmaMonomorphism_2986 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaMonomorphism_2986 v7
du_'92''92''45'isMagmaMonomorphism_2986 ::
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
du_'92''92''45'isMagmaMonomorphism_2986 v0
  = coe
      C_constructor_236
      (coe
         du_'92''92''45'isMagmaHomomorphism_2946
         (coe d_isQuasigroupHomomorphism_2962 (coe v0)))
      (coe d_injective_2964 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism.//-isMagmaMonomorphism
d_'47''47''45'isMagmaMonomorphism_2988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
d_'47''47''45'isMagmaMonomorphism_2988 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaMonomorphism_2988 v7
du_'47''47''45'isMagmaMonomorphism_2988 ::
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
du_'47''47''45'isMagmaMonomorphism_2988 v0
  = coe
      C_constructor_236
      (coe
         du_'47''47''45'isMagmaHomomorphism_2948
         (coe d_isQuasigroupHomomorphism_2962 (coe v0)))
      (coe d_injective_2964 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupMonomorphism._.isRelMonomorphism
d_isRelMonomorphism_2992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_2992 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_2992 v7
du_isRelMonomorphism_2992 ::
  T_IsQuasigroupMonomorphism_2954 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_2992 v0
  = coe
      du_isRelMonomorphism_234
      (coe du_'47''47''45'isMagmaMonomorphism_2988 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism
d_IsQuasigroupIsomorphism_2998 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsQuasigroupIsomorphism_2998
  = C_constructor_3050 T_IsQuasigroupMonomorphism_2954
                       (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism.isQuasigroupMonomorphism
d_isQuasigroupMonomorphism_3006 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsQuasigroupMonomorphism_2954
d_isQuasigroupMonomorphism_3006 v0
  = case coe v0 of
      C_constructor_3050 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism.surjective
d_surjective_3008 ::
  T_IsQuasigroupIsomorphism_2998 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_3008 v0
  = case coe v0 of
      C_constructor_3050 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.//-homo
d_'47''47''45'homo_3012 ::
  T_IsQuasigroupIsomorphism_2998 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_3012 v0
  = coe
      d_'47''47''45'homo_2938
      (coe
         d_isQuasigroupHomomorphism_2962
         (coe d_isQuasigroupMonomorphism_3006 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_3014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
d_'47''47''45'isMagmaHomomorphism_3014 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_3014 v7
du_'47''47''45'isMagmaHomomorphism_3014 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
du_'47''47''45'isMagmaHomomorphism_3014 v0
  = let v1 = d_isQuasigroupMonomorphism_3006 (coe v0) in
    coe
      (coe
         du_'47''47''45'isMagmaHomomorphism_2948
         (coe d_isQuasigroupHomomorphism_2962 (coe v1)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.//-isMagmaMonomorphism
d_'47''47''45'isMagmaMonomorphism_3016 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
d_'47''47''45'isMagmaMonomorphism_3016 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaMonomorphism_3016 v7
du_'47''47''45'isMagmaMonomorphism_3016 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
du_'47''47''45'isMagmaMonomorphism_3016 v0
  = coe
      du_'47''47''45'isMagmaMonomorphism_2988
      (coe d_isQuasigroupMonomorphism_3006 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.\\-homo
d_'92''92''45'homo_3018 ::
  T_IsQuasigroupIsomorphism_2998 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_3018 v0
  = coe
      d_'92''92''45'homo_2936
      (coe
         d_isQuasigroupHomomorphism_2962
         (coe d_isQuasigroupMonomorphism_3006 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_3020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
d_'92''92''45'isMagmaHomomorphism_3020 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_3020 v7
du_'92''92''45'isMagmaHomomorphism_3020 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
du_'92''92''45'isMagmaHomomorphism_3020 v0
  = let v1 = d_isQuasigroupMonomorphism_3006 (coe v0) in
    coe
      (coe
         du_'92''92''45'isMagmaHomomorphism_2946
         (coe d_isQuasigroupHomomorphism_2962 (coe v1)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.\\-isMagmaMonomorphism
d_'92''92''45'isMagmaMonomorphism_3022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
d_'92''92''45'isMagmaMonomorphism_3022 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaMonomorphism_3022 v7
du_'92''92''45'isMagmaMonomorphism_3022 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
du_'92''92''45'isMagmaMonomorphism_3022 v0
  = coe
      du_'92''92''45'isMagmaMonomorphism_2986
      (coe d_isQuasigroupMonomorphism_3006 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.injective
d_injective_3024 ::
  T_IsQuasigroupIsomorphism_2998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3024 v0
  = coe
      d_injective_2964 (coe d_isQuasigroupMonomorphism_3006 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_3026 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsQuasigroupHomomorphism_2920
d_isQuasigroupHomomorphism_3026 v0
  = coe
      d_isQuasigroupHomomorphism_2962
      (coe d_isQuasigroupMonomorphism_3006 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_3028 ::
  T_IsQuasigroupIsomorphism_2998 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3028 v0
  = coe
      d_isRelHomomorphism_2932
      (coe
         d_isQuasigroupHomomorphism_2962
         (coe d_isQuasigroupMonomorphism_3006 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.isRelMonomorphism
d_isRelMonomorphism_3030 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_3030 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_3030 v7
du_isRelMonomorphism_3030 ::
  T_IsQuasigroupIsomorphism_2998 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_3030 v0
  = let v1 = d_isQuasigroupMonomorphism_3006 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234
         (coe du_'47''47''45'isMagmaMonomorphism_2988 (coe v1)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.∙-homo
d_'8729''45'homo_3032 ::
  T_IsQuasigroupIsomorphism_2998 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_3032 v0
  = coe
      d_'8729''45'homo_2934
      (coe
         d_isQuasigroupHomomorphism_2962
         (coe d_isQuasigroupMonomorphism_3006 (coe v0)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_3034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
d_'8729''45'isMagmaHomomorphism_3034 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_3034 v7
du_'8729''45'isMagmaHomomorphism_3034 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
du_'8729''45'isMagmaHomomorphism_3034 v0
  = let v1 = d_isQuasigroupMonomorphism_3006 (coe v0) in
    coe
      (coe
         du_'8729''45'isMagmaHomomorphism_2944
         (coe d_isQuasigroupHomomorphism_2962 (coe v1)))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.∙-isMagmaMonomorphism
d_'8729''45'isMagmaMonomorphism_3036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
d_'8729''45'isMagmaMonomorphism_3036 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaMonomorphism_3036 v7
du_'8729''45'isMagmaMonomorphism_3036 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
du_'8729''45'isMagmaMonomorphism_3036 v0
  = coe
      du_'8729''45'isMagmaMonomorphism_2984
      (coe d_isQuasigroupMonomorphism_3006 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.cong
d_cong_3038 ::
  T_IsQuasigroupIsomorphism_2998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3038 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2932
         (coe
            d_isQuasigroupHomomorphism_2962
            (coe d_isQuasigroupMonomorphism_3006 (coe v0))))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism.∙-isMagmaIsomorphism
d_'8729''45'isMagmaIsomorphism_3040 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
d_'8729''45'isMagmaIsomorphism_3040 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaIsomorphism_3040 v7
du_'8729''45'isMagmaIsomorphism_3040 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
du_'8729''45'isMagmaIsomorphism_3040 v0
  = coe
      C_constructor_268
      (coe
         du_'8729''45'isMagmaMonomorphism_2984
         (coe d_isQuasigroupMonomorphism_3006 (coe v0)))
      (coe d_surjective_3008 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism.\\-isMagmaIsomorphism
d_'92''92''45'isMagmaIsomorphism_3042 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
d_'92''92''45'isMagmaIsomorphism_3042 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      v7
  = du_'92''92''45'isMagmaIsomorphism_3042 v7
du_'92''92''45'isMagmaIsomorphism_3042 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
du_'92''92''45'isMagmaIsomorphism_3042 v0
  = coe
      C_constructor_268
      (coe
         du_'92''92''45'isMagmaMonomorphism_2986
         (coe d_isQuasigroupMonomorphism_3006 (coe v0)))
      (coe d_surjective_3008 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism.//-isMagmaIsomorphism
d_'47''47''45'isMagmaIsomorphism_3044 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
d_'47''47''45'isMagmaIsomorphism_3044 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      v7
  = du_'47''47''45'isMagmaIsomorphism_3044 v7
du_'47''47''45'isMagmaIsomorphism_3044 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
du_'47''47''45'isMagmaIsomorphism_3044 v0
  = coe
      C_constructor_268
      (coe
         du_'47''47''45'isMagmaMonomorphism_2988
         (coe d_isQuasigroupMonomorphism_3006 (coe v0)))
      (coe d_surjective_3008 (coe v0))
-- Algebra.Morphism.Structures.QuasigroupMorphisms.IsQuasigroupIsomorphism._.isRelIsomorphism
d_isRelIsomorphism_3048 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawQuasigroup_350 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_3048 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_3048 v7
du_isRelIsomorphism_3048 ::
  T_IsQuasigroupIsomorphism_2998 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_3048 v0
  = coe
      du_isRelIsomorphism_266
      (coe du_'47''47''45'isMagmaIsomorphism_3044 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._._≈_
d__'8776'__3074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__3074 = erased
-- Algebra.Morphism.Structures.LoopMorphisms._.Carrier
d_Carrier_3080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 -> ()
d_Carrier_3080 = erased
-- Algebra.Morphism.Structures.LoopMorphisms._.ε
d_ε_3086 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 -> AgdaAny
d_ε_3086 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_ε_3086 v4
du_ε_3086 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 -> AgdaAny
du_ε_3086 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_ε_420 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.Homomorphic₀
d_Homomorphic'8320'_3116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_3116 = erased
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism
d_IsQuasigroupHomomorphism_3126 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism
d_IsQuasigroupIsomorphism_3130 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism
d_IsQuasigroupMonomorphism_3134 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaHomomorphism
d_IsMagmaHomomorphism_3140 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism
d_IsMagmaIsomorphism_3144 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism
d_IsMagmaMonomorphism_3148 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaHomomorphism.homo
d_homo_3154 ::
  T_IsMagmaHomomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3154 v0 = coe d_homo_204 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_3156 ::
  T_IsMagmaHomomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3156 v0 = coe d_isRelHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaHomomorphism.cong
d_cong_3158 ::
  T_IsMagmaHomomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3158 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.homo
d_homo_3162 ::
  T_IsMagmaIsomorphism_240 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3162 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.injective
d_injective_3164 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3164 v0
  = coe d_injective_224 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3166 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3166 v0
  = coe
      d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_3168 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_3168 v0
  = coe d_isMagmaMonomorphism_248 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_3170 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3170 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_3172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_3172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_3172
du_isRelIsomorphism_3172 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_3172 v0 v1 = coe du_isRelIsomorphism_266 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_3174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_3174 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_3174 v7
du_isRelMonomorphism_3174 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_3174 v0
  = coe
      du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.surjective
d_surjective_3176 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_3176 v0 = coe d_surjective_250 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaIsomorphism.cong
d_cong_3178 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3178 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_222
            (coe d_isMagmaMonomorphism_248 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.homo
d_homo_3182 ::
  T_IsMagmaMonomorphism_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3182 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.injective
d_injective_3184 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3184 v0 = coe d_injective_224 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3186 ::
  T_IsMagmaMonomorphism_214 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3186 v0
  = coe d_isMagmaHomomorphism_222 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_3188 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3188 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_3190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_3190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_3190
du_isRelMonomorphism_3190 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_3190 v0 v1 = coe du_isRelMonomorphism_234 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.//.IsMagmaMonomorphism.cong
d_cong_3192 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.//-homo
d_'47''47''45'homo_3196 ::
  T_IsQuasigroupHomomorphism_2920 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_3196 v0 = coe d_'47''47''45'homo_2938 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_3198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
d_'47''47''45'isMagmaHomomorphism_3198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'47''47''45'isMagmaHomomorphism_3198
du_'47''47''45'isMagmaHomomorphism_3198 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
du_'47''47''45'isMagmaHomomorphism_3198 v0 v1
  = coe du_'47''47''45'isMagmaHomomorphism_2948 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.\\-homo
d_'92''92''45'homo_3200 ::
  T_IsQuasigroupHomomorphism_2920 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_3200 v0 = coe d_'92''92''45'homo_2936 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_3202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
d_'92''92''45'isMagmaHomomorphism_3202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'92''92''45'isMagmaHomomorphism_3202
du_'92''92''45'isMagmaHomomorphism_3202 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
du_'92''92''45'isMagmaHomomorphism_3202 v0 v1
  = coe du_'92''92''45'isMagmaHomomorphism_2946 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.isRelHomomorphism
d_isRelHomomorphism_3204 ::
  T_IsQuasigroupHomomorphism_2920 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3204 v0 = coe d_isRelHomomorphism_2932 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.∙-homo
d_'8729''45'homo_3206 ::
  T_IsQuasigroupHomomorphism_2920 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_3206 v0 = coe d_'8729''45'homo_2934 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_3208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
d_'8729''45'isMagmaHomomorphism_3208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8729''45'isMagmaHomomorphism_3208
du_'8729''45'isMagmaHomomorphism_3208 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupHomomorphism_2920 -> T_IsMagmaHomomorphism_194
du_'8729''45'isMagmaHomomorphism_3208 v0 v1
  = coe du_'8729''45'isMagmaHomomorphism_2944 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupHomomorphism.cong
d_cong_3210 ::
  T_IsQuasigroupHomomorphism_2920 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3210 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_2932 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.//-homo
d_'47''47''45'homo_3214 ::
  T_IsQuasigroupIsomorphism_2998 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_3214 v0
  = coe
      d_'47''47''45'homo_2938
      (coe
         d_isQuasigroupHomomorphism_2962
         (coe d_isQuasigroupMonomorphism_3006 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_3216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
d_'47''47''45'isMagmaHomomorphism_3216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_3216 v7
du_'47''47''45'isMagmaHomomorphism_3216 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
du_'47''47''45'isMagmaHomomorphism_3216 v0
  = let v1 = d_isQuasigroupMonomorphism_3006 (coe v0) in
    coe
      (coe
         du_'47''47''45'isMagmaHomomorphism_2948
         (coe d_isQuasigroupHomomorphism_2962 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.//-isMagmaIsomorphism
d_'47''47''45'isMagmaIsomorphism_3218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
d_'47''47''45'isMagmaIsomorphism_3218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'47''47''45'isMagmaIsomorphism_3218
du_'47''47''45'isMagmaIsomorphism_3218 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
du_'47''47''45'isMagmaIsomorphism_3218 v0 v1
  = coe du_'47''47''45'isMagmaIsomorphism_3044 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.//-isMagmaMonomorphism
d_'47''47''45'isMagmaMonomorphism_3220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
d_'47''47''45'isMagmaMonomorphism_3220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaMonomorphism_3220 v7
du_'47''47''45'isMagmaMonomorphism_3220 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
du_'47''47''45'isMagmaMonomorphism_3220 v0
  = coe
      du_'47''47''45'isMagmaMonomorphism_2988
      (coe d_isQuasigroupMonomorphism_3006 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.\\-homo
d_'92''92''45'homo_3222 ::
  T_IsQuasigroupIsomorphism_2998 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_3222 v0
  = coe
      d_'92''92''45'homo_2936
      (coe
         d_isQuasigroupHomomorphism_2962
         (coe d_isQuasigroupMonomorphism_3006 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_3224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
d_'92''92''45'isMagmaHomomorphism_3224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_3224 v7
du_'92''92''45'isMagmaHomomorphism_3224 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
du_'92''92''45'isMagmaHomomorphism_3224 v0
  = let v1 = d_isQuasigroupMonomorphism_3006 (coe v0) in
    coe
      (coe
         du_'92''92''45'isMagmaHomomorphism_2946
         (coe d_isQuasigroupHomomorphism_2962 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.\\-isMagmaIsomorphism
d_'92''92''45'isMagmaIsomorphism_3226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
d_'92''92''45'isMagmaIsomorphism_3226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'92''92''45'isMagmaIsomorphism_3226
du_'92''92''45'isMagmaIsomorphism_3226 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
du_'92''92''45'isMagmaIsomorphism_3226 v0 v1
  = coe du_'92''92''45'isMagmaIsomorphism_3042 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.\\-isMagmaMonomorphism
d_'92''92''45'isMagmaMonomorphism_3228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
d_'92''92''45'isMagmaMonomorphism_3228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaMonomorphism_3228 v7
du_'92''92''45'isMagmaMonomorphism_3228 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
du_'92''92''45'isMagmaMonomorphism_3228 v0
  = coe
      du_'92''92''45'isMagmaMonomorphism_2986
      (coe d_isQuasigroupMonomorphism_3006 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.injective
d_injective_3230 ::
  T_IsQuasigroupIsomorphism_2998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3230 v0
  = coe
      d_injective_2964 (coe d_isQuasigroupMonomorphism_3006 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_3232 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsQuasigroupHomomorphism_2920
d_isQuasigroupHomomorphism_3232 v0
  = coe
      d_isQuasigroupHomomorphism_2962
      (coe d_isQuasigroupMonomorphism_3006 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.isQuasigroupMonomorphism
d_isQuasigroupMonomorphism_3234 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsQuasigroupMonomorphism_2954
d_isQuasigroupMonomorphism_3234 v0
  = coe d_isQuasigroupMonomorphism_3006 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.isRelHomomorphism
d_isRelHomomorphism_3236 ::
  T_IsQuasigroupIsomorphism_2998 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3236 v0
  = coe
      d_isRelHomomorphism_2932
      (coe
         d_isQuasigroupHomomorphism_2962
         (coe d_isQuasigroupMonomorphism_3006 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.isRelIsomorphism
d_isRelIsomorphism_3238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_3238 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelIsomorphism_3238 v7
du_isRelIsomorphism_3238 ::
  T_IsQuasigroupIsomorphism_2998 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_3238 v0
  = coe
      du_isRelIsomorphism_266
      (coe du_'47''47''45'isMagmaIsomorphism_3044 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.isRelMonomorphism
d_isRelMonomorphism_3240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_3240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_3240 v7
du_isRelMonomorphism_3240 ::
  T_IsQuasigroupIsomorphism_2998 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_3240 v0
  = let v1 = d_isQuasigroupMonomorphism_3006 (coe v0) in
    coe
      (coe
         du_isRelMonomorphism_234
         (coe du_'47''47''45'isMagmaMonomorphism_2988 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.surjective
d_surjective_3242 ::
  T_IsQuasigroupIsomorphism_2998 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_3242 v0 = coe d_surjective_3008 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.∙-homo
d_'8729''45'homo_3244 ::
  T_IsQuasigroupIsomorphism_2998 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_3244 v0
  = coe
      d_'8729''45'homo_2934
      (coe
         d_isQuasigroupHomomorphism_2962
         (coe d_isQuasigroupMonomorphism_3006 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_3246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
d_'8729''45'isMagmaHomomorphism_3246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_3246 v7
du_'8729''45'isMagmaHomomorphism_3246 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaHomomorphism_194
du_'8729''45'isMagmaHomomorphism_3246 v0
  = let v1 = d_isQuasigroupMonomorphism_3006 (coe v0) in
    coe
      (coe
         du_'8729''45'isMagmaHomomorphism_2944
         (coe d_isQuasigroupHomomorphism_2962 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.∙-isMagmaIsomorphism
d_'8729''45'isMagmaIsomorphism_3248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
d_'8729''45'isMagmaIsomorphism_3248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8729''45'isMagmaIsomorphism_3248
du_'8729''45'isMagmaIsomorphism_3248 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaIsomorphism_240
du_'8729''45'isMagmaIsomorphism_3248 v0 v1
  = coe du_'8729''45'isMagmaIsomorphism_3040 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.∙-isMagmaMonomorphism
d_'8729''45'isMagmaMonomorphism_3250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
d_'8729''45'isMagmaMonomorphism_3250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaMonomorphism_3250 v7
du_'8729''45'isMagmaMonomorphism_3250 ::
  T_IsQuasigroupIsomorphism_2998 -> T_IsMagmaMonomorphism_214
du_'8729''45'isMagmaMonomorphism_3250 v0
  = coe
      du_'8729''45'isMagmaMonomorphism_2984
      (coe d_isQuasigroupMonomorphism_3006 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupIsomorphism.cong
d_cong_3252 ::
  T_IsQuasigroupIsomorphism_2998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3252 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2932
         (coe
            d_isQuasigroupHomomorphism_2962
            (coe d_isQuasigroupMonomorphism_3006 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.//-homo
d_'47''47''45'homo_3256 ::
  T_IsQuasigroupMonomorphism_2954 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_3256 v0
  = coe
      d_'47''47''45'homo_2938
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_3258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
d_'47''47''45'isMagmaHomomorphism_3258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_3258 v7
du_'47''47''45'isMagmaHomomorphism_3258 ::
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
du_'47''47''45'isMagmaHomomorphism_3258 v0
  = coe
      du_'47''47''45'isMagmaHomomorphism_2948
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.//-isMagmaMonomorphism
d_'47''47''45'isMagmaMonomorphism_3260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
d_'47''47''45'isMagmaMonomorphism_3260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'47''47''45'isMagmaMonomorphism_3260
du_'47''47''45'isMagmaMonomorphism_3260 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
du_'47''47''45'isMagmaMonomorphism_3260 v0 v1
  = coe du_'47''47''45'isMagmaMonomorphism_2988 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.\\-homo
d_'92''92''45'homo_3262 ::
  T_IsQuasigroupMonomorphism_2954 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_3262 v0
  = coe
      d_'92''92''45'homo_2936
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_3264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
d_'92''92''45'isMagmaHomomorphism_3264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_3264 v7
du_'92''92''45'isMagmaHomomorphism_3264 ::
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
du_'92''92''45'isMagmaHomomorphism_3264 v0
  = coe
      du_'92''92''45'isMagmaHomomorphism_2946
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.\\-isMagmaMonomorphism
d_'92''92''45'isMagmaMonomorphism_3266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
d_'92''92''45'isMagmaMonomorphism_3266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'92''92''45'isMagmaMonomorphism_3266
du_'92''92''45'isMagmaMonomorphism_3266 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
du_'92''92''45'isMagmaMonomorphism_3266 v0 v1
  = coe du_'92''92''45'isMagmaMonomorphism_2986 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.injective
d_injective_3268 ::
  T_IsQuasigroupMonomorphism_2954 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3268 v0 = coe d_injective_2964 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_3270 ::
  T_IsQuasigroupMonomorphism_2954 -> T_IsQuasigroupHomomorphism_2920
d_isQuasigroupHomomorphism_3270 v0
  = coe d_isQuasigroupHomomorphism_2962 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.isRelHomomorphism
d_isRelHomomorphism_3272 ::
  T_IsQuasigroupMonomorphism_2954 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3272 v0
  = coe
      d_isRelHomomorphism_2932
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.isRelMonomorphism
d_isRelMonomorphism_3274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_3274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_3274 v7
du_isRelMonomorphism_3274 ::
  T_IsQuasigroupMonomorphism_2954 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_3274 v0
  = coe
      du_isRelMonomorphism_234
      (coe du_'47''47''45'isMagmaMonomorphism_2988 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.∙-homo
d_'8729''45'homo_3276 ::
  T_IsQuasigroupMonomorphism_2954 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_3276 v0
  = coe
      d_'8729''45'homo_2934
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_3278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
d_'8729''45'isMagmaHomomorphism_3278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_3278 v7
du_'8729''45'isMagmaHomomorphism_3278 ::
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaHomomorphism_194
du_'8729''45'isMagmaHomomorphism_3278 v0
  = coe
      du_'8729''45'isMagmaHomomorphism_2944
      (coe d_isQuasigroupHomomorphism_2962 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.∙-isMagmaMonomorphism
d_'8729''45'isMagmaMonomorphism_3280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
d_'8729''45'isMagmaMonomorphism_3280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8729''45'isMagmaMonomorphism_3280
du_'8729''45'isMagmaMonomorphism_3280 ::
  (AgdaAny -> AgdaAny) ->
  T_IsQuasigroupMonomorphism_2954 -> T_IsMagmaMonomorphism_214
du_'8729''45'isMagmaMonomorphism_3280 v0 v1
  = coe du_'8729''45'isMagmaMonomorphism_2984 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.IsQuasigroupMonomorphism.cong
d_cong_3282 ::
  T_IsQuasigroupMonomorphism_2954 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3282 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2932
         (coe d_isQuasigroupHomomorphism_2962 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaHomomorphism
d_IsMagmaHomomorphism_3286 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism
d_IsMagmaIsomorphism_3290 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism
d_IsMagmaMonomorphism_3294 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaHomomorphism.homo
d_homo_3300 ::
  T_IsMagmaHomomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3300 v0 = coe d_homo_204 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_3302 ::
  T_IsMagmaHomomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3302 v0 = coe d_isRelHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaHomomorphism.cong
d_cong_3304 ::
  T_IsMagmaHomomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3304 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.homo
d_homo_3308 ::
  T_IsMagmaIsomorphism_240 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3308 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.injective
d_injective_3310 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3310 v0
  = coe d_injective_224 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3312 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3312 v0
  = coe
      d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_3314 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_3314 v0
  = coe d_isMagmaMonomorphism_248 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_3316 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3316 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_3318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_3318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_3318
du_isRelIsomorphism_3318 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_3318 v0 v1 = coe du_isRelIsomorphism_266 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_3320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_3320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_3320 v7
du_isRelMonomorphism_3320 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_3320 v0
  = coe
      du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.surjective
d_surjective_3322 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_3322 v0 = coe d_surjective_250 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaIsomorphism.cong
d_cong_3324 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3324 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_222
            (coe d_isMagmaMonomorphism_248 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.homo
d_homo_3328 ::
  T_IsMagmaMonomorphism_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3328 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.injective
d_injective_3330 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3330 v0 = coe d_injective_224 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3332 ::
  T_IsMagmaMonomorphism_214 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3332 v0
  = coe d_isMagmaHomomorphism_222 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_3334 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3334 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_3336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_3336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_3336
du_isRelMonomorphism_3336 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_3336 v0 v1 = coe du_isRelMonomorphism_234 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.\\.IsMagmaMonomorphism.cong
d_cong_3338 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3338 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaHomomorphism
d_IsMagmaHomomorphism_3342 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism
d_IsMagmaIsomorphism_3346 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism
d_IsMagmaMonomorphism_3350 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaHomomorphism.homo
d_homo_3356 ::
  T_IsMagmaHomomorphism_194 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3356 v0 = coe d_homo_204 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaHomomorphism.isRelHomomorphism
d_isRelHomomorphism_3358 ::
  T_IsMagmaHomomorphism_194 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3358 v0 = coe d_isRelHomomorphism_202 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaHomomorphism.cong
d_cong_3360 ::
  T_IsMagmaHomomorphism_194 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3360 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe d_isRelHomomorphism_202 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.homo
d_homo_3364 ::
  T_IsMagmaIsomorphism_240 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3364 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.injective
d_injective_3366 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3366 v0
  = coe d_injective_224 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3368 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3368 v0
  = coe
      d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.isMagmaMonomorphism
d_isMagmaMonomorphism_3370 ::
  T_IsMagmaIsomorphism_240 -> T_IsMagmaMonomorphism_214
d_isMagmaMonomorphism_3370 v0
  = coe d_isMagmaMonomorphism_248 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.isRelHomomorphism
d_isRelHomomorphism_3372 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3372 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_222 (coe d_isMagmaMonomorphism_248 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.isRelIsomorphism
d_isRelIsomorphism_3374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
d_isRelIsomorphism_3374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelIsomorphism_3374
du_isRelIsomorphism_3374 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelIsomorphism_98
du_isRelIsomorphism_3374 v0 v1 = coe du_isRelIsomorphism_266 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.isRelMonomorphism
d_isRelMonomorphism_3376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_3376 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isRelMonomorphism_3376 v7
du_isRelMonomorphism_3376 ::
  T_IsMagmaIsomorphism_240 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_3376 v0
  = coe
      du_isRelMonomorphism_234 (coe d_isMagmaMonomorphism_248 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.surjective
d_surjective_3378 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_3378 v0 = coe d_surjective_250 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaIsomorphism.cong
d_cong_3380 ::
  T_IsMagmaIsomorphism_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3380 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_222
            (coe d_isMagmaMonomorphism_248 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.homo
d_homo_3384 ::
  T_IsMagmaMonomorphism_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3384 v0
  = coe d_homo_204 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.injective
d_injective_3386 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3386 v0 = coe d_injective_224 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3388 ::
  T_IsMagmaMonomorphism_214 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3388 v0
  = coe d_isMagmaHomomorphism_222 (coe v0)
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.isRelHomomorphism
d_isRelHomomorphism_3390 ::
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3390 v0
  = coe
      d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.isRelMonomorphism
d_isRelMonomorphism_3392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
d_isRelMonomorphism_3392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isRelMonomorphism_3392
du_isRelMonomorphism_3392 ::
  (AgdaAny -> AgdaAny) ->
  T_IsMagmaMonomorphism_214 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_66
du_isRelMonomorphism_3392 v0 v1 = coe du_isRelMonomorphism_234 v1
-- Algebra.Morphism.Structures.LoopMorphisms._.∙.IsMagmaMonomorphism.cong
d_cong_3394 ::
  T_IsMagmaMonomorphism_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3394 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202 (coe d_isMagmaHomomorphism_222 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism
d_IsLoopHomomorphism_3398 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsLoopHomomorphism_3398
  = C_constructor_3428 T_IsQuasigroupHomomorphism_2920 AgdaAny
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_3406 ::
  T_IsLoopHomomorphism_3398 -> T_IsQuasigroupHomomorphism_2920
d_isQuasigroupHomomorphism_3406 v0
  = case coe v0 of
      C_constructor_3428 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism.ε-homo
d_ε'45'homo_3408 :: T_IsLoopHomomorphism_3398 -> AgdaAny
d_ε'45'homo_3408 v0
  = case coe v0 of
      C_constructor_3428 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.//-homo
d_'47''47''45'homo_3412 ::
  T_IsLoopHomomorphism_3398 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_3412 v0
  = coe
      d_'47''47''45'homo_2938
      (coe d_isQuasigroupHomomorphism_3406 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_3414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopHomomorphism_3398 -> T_IsMagmaHomomorphism_194
d_'47''47''45'isMagmaHomomorphism_3414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_3414 v7
du_'47''47''45'isMagmaHomomorphism_3414 ::
  T_IsLoopHomomorphism_3398 -> T_IsMagmaHomomorphism_194
du_'47''47''45'isMagmaHomomorphism_3414 v0
  = coe
      du_'47''47''45'isMagmaHomomorphism_2948
      (coe d_isQuasigroupHomomorphism_3406 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.\\-homo
d_'92''92''45'homo_3416 ::
  T_IsLoopHomomorphism_3398 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_3416 v0
  = coe
      d_'92''92''45'homo_2936
      (coe d_isQuasigroupHomomorphism_3406 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_3418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopHomomorphism_3398 -> T_IsMagmaHomomorphism_194
d_'92''92''45'isMagmaHomomorphism_3418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_3418 v7
du_'92''92''45'isMagmaHomomorphism_3418 ::
  T_IsLoopHomomorphism_3398 -> T_IsMagmaHomomorphism_194
du_'92''92''45'isMagmaHomomorphism_3418 v0
  = coe
      du_'92''92''45'isMagmaHomomorphism_2946
      (coe d_isQuasigroupHomomorphism_3406 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_3420 ::
  T_IsLoopHomomorphism_3398 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3420 v0
  = coe
      d_isRelHomomorphism_2932
      (coe d_isQuasigroupHomomorphism_3406 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.∙-homo
d_'8729''45'homo_3422 ::
  T_IsLoopHomomorphism_3398 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_3422 v0
  = coe
      d_'8729''45'homo_2934
      (coe d_isQuasigroupHomomorphism_3406 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_3424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopHomomorphism_3398 -> T_IsMagmaHomomorphism_194
d_'8729''45'isMagmaHomomorphism_3424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_3424 v7
du_'8729''45'isMagmaHomomorphism_3424 ::
  T_IsLoopHomomorphism_3398 -> T_IsMagmaHomomorphism_194
du_'8729''45'isMagmaHomomorphism_3424 v0
  = coe
      du_'8729''45'isMagmaHomomorphism_2944
      (coe d_isQuasigroupHomomorphism_3406 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopHomomorphism._.cong
d_cong_3426 ::
  T_IsLoopHomomorphism_3398 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3426 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2932
         (coe d_isQuasigroupHomomorphism_3406 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism
d_IsLoopMonomorphism_3432 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsLoopMonomorphism_3432
  = C_constructor_3466 T_IsLoopHomomorphism_3398
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism.isLoopHomomorphism
d_isLoopHomomorphism_3440 ::
  T_IsLoopMonomorphism_3432 -> T_IsLoopHomomorphism_3398
d_isLoopHomomorphism_3440 v0
  = case coe v0 of
      C_constructor_3466 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism.injective
d_injective_3442 ::
  T_IsLoopMonomorphism_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3442 v0
  = case coe v0 of
      C_constructor_3466 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.//-homo
d_'47''47''45'homo_3446 ::
  T_IsLoopMonomorphism_3432 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_3446 v0
  = coe
      d_'47''47''45'homo_2938
      (coe
         d_isQuasigroupHomomorphism_3406
         (coe d_isLoopHomomorphism_3440 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_3448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopMonomorphism_3432 -> T_IsMagmaHomomorphism_194
d_'47''47''45'isMagmaHomomorphism_3448 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_3448 v7
du_'47''47''45'isMagmaHomomorphism_3448 ::
  T_IsLoopMonomorphism_3432 -> T_IsMagmaHomomorphism_194
du_'47''47''45'isMagmaHomomorphism_3448 v0
  = let v1 = d_isLoopHomomorphism_3440 (coe v0) in
    coe
      (coe
         du_'47''47''45'isMagmaHomomorphism_2948
         (coe d_isQuasigroupHomomorphism_3406 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.\\-homo
d_'92''92''45'homo_3450 ::
  T_IsLoopMonomorphism_3432 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_3450 v0
  = coe
      d_'92''92''45'homo_2936
      (coe
         d_isQuasigroupHomomorphism_3406
         (coe d_isLoopHomomorphism_3440 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_3452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopMonomorphism_3432 -> T_IsMagmaHomomorphism_194
d_'92''92''45'isMagmaHomomorphism_3452 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_3452 v7
du_'92''92''45'isMagmaHomomorphism_3452 ::
  T_IsLoopMonomorphism_3432 -> T_IsMagmaHomomorphism_194
du_'92''92''45'isMagmaHomomorphism_3452 v0
  = let v1 = d_isLoopHomomorphism_3440 (coe v0) in
    coe
      (coe
         du_'92''92''45'isMagmaHomomorphism_2946
         (coe d_isQuasigroupHomomorphism_3406 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_3454 ::
  T_IsLoopMonomorphism_3432 -> T_IsQuasigroupHomomorphism_2920
d_isQuasigroupHomomorphism_3454 v0
  = coe
      d_isQuasigroupHomomorphism_3406
      (coe d_isLoopHomomorphism_3440 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_3456 ::
  T_IsLoopMonomorphism_3432 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3456 v0
  = coe
      d_isRelHomomorphism_2932
      (coe
         d_isQuasigroupHomomorphism_3406
         (coe d_isLoopHomomorphism_3440 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.ε-homo
d_ε'45'homo_3458 :: T_IsLoopMonomorphism_3432 -> AgdaAny
d_ε'45'homo_3458 v0
  = coe d_ε'45'homo_3408 (coe d_isLoopHomomorphism_3440 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.∙-homo
d_'8729''45'homo_3460 ::
  T_IsLoopMonomorphism_3432 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_3460 v0
  = coe
      d_'8729''45'homo_2934
      (coe
         d_isQuasigroupHomomorphism_3406
         (coe d_isLoopHomomorphism_3440 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_3462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopMonomorphism_3432 -> T_IsMagmaHomomorphism_194
d_'8729''45'isMagmaHomomorphism_3462 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_3462 v7
du_'8729''45'isMagmaHomomorphism_3462 ::
  T_IsLoopMonomorphism_3432 -> T_IsMagmaHomomorphism_194
du_'8729''45'isMagmaHomomorphism_3462 v0
  = let v1 = d_isLoopHomomorphism_3440 (coe v0) in
    coe
      (coe
         du_'8729''45'isMagmaHomomorphism_2944
         (coe d_isQuasigroupHomomorphism_3406 (coe v1)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopMonomorphism._.cong
d_cong_3464 ::
  T_IsLoopMonomorphism_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3464 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2932
         (coe
            d_isQuasigroupHomomorphism_3406
            (coe d_isLoopHomomorphism_3440 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism
d_IsLoopIsomorphism_3470 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsLoopIsomorphism_3470
  = C_constructor_3508 T_IsLoopMonomorphism_3432
                       (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism.isLoopMonomorphism
d_isLoopMonomorphism_3478 ::
  T_IsLoopIsomorphism_3470 -> T_IsLoopMonomorphism_3432
d_isLoopMonomorphism_3478 v0
  = case coe v0 of
      C_constructor_3508 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism.surjective
d_surjective_3480 ::
  T_IsLoopIsomorphism_3470 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_3480 v0
  = case coe v0 of
      C_constructor_3508 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.//-homo
d_'47''47''45'homo_3484 ::
  T_IsLoopIsomorphism_3470 -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'homo_3484 v0
  = coe
      d_'47''47''45'homo_2938
      (coe
         d_isQuasigroupHomomorphism_3406
         (coe
            d_isLoopHomomorphism_3440
            (coe d_isLoopMonomorphism_3478 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.//-isMagmaHomomorphism
d_'47''47''45'isMagmaHomomorphism_3486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopIsomorphism_3470 -> T_IsMagmaHomomorphism_194
d_'47''47''45'isMagmaHomomorphism_3486 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'47''47''45'isMagmaHomomorphism_3486 v7
du_'47''47''45'isMagmaHomomorphism_3486 ::
  T_IsLoopIsomorphism_3470 -> T_IsMagmaHomomorphism_194
du_'47''47''45'isMagmaHomomorphism_3486 v0
  = let v1 = d_isLoopMonomorphism_3478 (coe v0) in
    coe
      (let v2 = d_isLoopHomomorphism_3440 (coe v1) in
       coe
         (coe
            du_'47''47''45'isMagmaHomomorphism_2948
            (coe d_isQuasigroupHomomorphism_3406 (coe v2))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.\\-homo
d_'92''92''45'homo_3488 ::
  T_IsLoopIsomorphism_3470 -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'homo_3488 v0
  = coe
      d_'92''92''45'homo_2936
      (coe
         d_isQuasigroupHomomorphism_3406
         (coe
            d_isLoopHomomorphism_3440
            (coe d_isLoopMonomorphism_3478 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.\\-isMagmaHomomorphism
d_'92''92''45'isMagmaHomomorphism_3490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopIsomorphism_3470 -> T_IsMagmaHomomorphism_194
d_'92''92''45'isMagmaHomomorphism_3490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       v7
  = du_'92''92''45'isMagmaHomomorphism_3490 v7
du_'92''92''45'isMagmaHomomorphism_3490 ::
  T_IsLoopIsomorphism_3470 -> T_IsMagmaHomomorphism_194
du_'92''92''45'isMagmaHomomorphism_3490 v0
  = let v1 = d_isLoopMonomorphism_3478 (coe v0) in
    coe
      (let v2 = d_isLoopHomomorphism_3440 (coe v1) in
       coe
         (coe
            du_'92''92''45'isMagmaHomomorphism_2946
            (coe d_isQuasigroupHomomorphism_3406 (coe v2))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.injective
d_injective_3492 ::
  T_IsLoopIsomorphism_3470 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3492 v0
  = coe d_injective_3442 (coe d_isLoopMonomorphism_3478 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.isLoopHomomorphism
d_isLoopHomomorphism_3494 ::
  T_IsLoopIsomorphism_3470 -> T_IsLoopHomomorphism_3398
d_isLoopHomomorphism_3494 v0
  = coe
      d_isLoopHomomorphism_3440 (coe d_isLoopMonomorphism_3478 (coe v0))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.isQuasigroupHomomorphism
d_isQuasigroupHomomorphism_3496 ::
  T_IsLoopIsomorphism_3470 -> T_IsQuasigroupHomomorphism_2920
d_isQuasigroupHomomorphism_3496 v0
  = coe
      d_isQuasigroupHomomorphism_3406
      (coe
         d_isLoopHomomorphism_3440 (coe d_isLoopMonomorphism_3478 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_3498 ::
  T_IsLoopIsomorphism_3470 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3498 v0
  = coe
      d_isRelHomomorphism_2932
      (coe
         d_isQuasigroupHomomorphism_3406
         (coe
            d_isLoopHomomorphism_3440
            (coe d_isLoopMonomorphism_3478 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.ε-homo
d_ε'45'homo_3500 :: T_IsLoopIsomorphism_3470 -> AgdaAny
d_ε'45'homo_3500 v0
  = coe
      d_ε'45'homo_3408
      (coe
         d_isLoopHomomorphism_3440 (coe d_isLoopMonomorphism_3478 (coe v0)))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.∙-homo
d_'8729''45'homo_3502 ::
  T_IsLoopIsomorphism_3470 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_3502 v0
  = coe
      d_'8729''45'homo_2934
      (coe
         d_isQuasigroupHomomorphism_3406
         (coe
            d_isLoopHomomorphism_3440
            (coe d_isLoopMonomorphism_3478 (coe v0))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.∙-isMagmaHomomorphism
d_'8729''45'isMagmaHomomorphism_3504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawLoop_392 ->
  (AgdaAny -> AgdaAny) ->
  T_IsLoopIsomorphism_3470 -> T_IsMagmaHomomorphism_194
d_'8729''45'isMagmaHomomorphism_3504 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'isMagmaHomomorphism_3504 v7
du_'8729''45'isMagmaHomomorphism_3504 ::
  T_IsLoopIsomorphism_3470 -> T_IsMagmaHomomorphism_194
du_'8729''45'isMagmaHomomorphism_3504 v0
  = let v1 = d_isLoopMonomorphism_3478 (coe v0) in
    coe
      (let v2 = d_isLoopHomomorphism_3440 (coe v1) in
       coe
         (coe
            du_'8729''45'isMagmaHomomorphism_2944
            (coe d_isQuasigroupHomomorphism_3406 (coe v2))))
-- Algebra.Morphism.Structures.LoopMorphisms.IsLoopIsomorphism._.cong
d_cong_3506 ::
  T_IsLoopIsomorphism_3470 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3506 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_2932
         (coe
            d_isQuasigroupHomomorphism_3406
            (coe
               d_isLoopHomomorphism_3440
               (coe d_isLoopMonomorphism_3478 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._._≈_
d__'8776'__3530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__3530 = erased
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._._⋆
d__'8902'_3534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  AgdaAny -> AgdaAny
d__'8902'_3534 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8902'_3534 v4
du__'8902'_3534 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  AgdaAny -> AgdaAny
du__'8902'_3534 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8902'_468 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.Carrier
d_Carrier_3548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 -> ()
d_Carrier_3548 = erased
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.Homomorphic₁
d_Homomorphic'8321'_3584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_3584 = erased
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism
d_IsSemiringHomomorphism_3592 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism
d_IsSemiringIsomorphism_3596 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism
d_IsSemiringMonomorphism_3600 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.*-homo
d_'42''45'homo_3606 ::
  T_IsSemiringHomomorphism_1366 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3606 v0
  = coe
      d_'42''45'homo_992 (coe d_isNearSemiringHomomorphism_1374 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1366 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_3608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3608 v7
du_'42''45'isMagmaHomomorphism_3608 ::
  T_IsSemiringHomomorphism_1366 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_3608 v0
  = coe
      du_'42''45'isMagmaHomomorphism_1006
      (coe d_isNearSemiringHomomorphism_1374 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1366 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_3610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidHomomorphism_3610
du_'42''45'isMonoidHomomorphism_3610 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringHomomorphism_1366 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_3610 v0 v1
  = coe du_'42''45'isMonoidHomomorphism_1396 v1
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.homo
d_homo_3612 ::
  T_IsSemiringHomomorphism_1366 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3612 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1374 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3614 ::
  T_IsSemiringHomomorphism_1366 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3614 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1374 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3616 ::
  T_IsSemiringHomomorphism_1366 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_3616 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe d_isNearSemiringHomomorphism_1374 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.ε-homo
d_ε'45'homo_3618 :: T_IsSemiringHomomorphism_1366 -> AgdaAny
d_ε'45'homo_3618 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe d_isNearSemiringHomomorphism_1374 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.1#-homo
d_1'35''45'homo_3620 :: T_IsSemiringHomomorphism_1366 -> AgdaAny
d_1'35''45'homo_3620 v0 = coe d_1'35''45'homo_1376 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3622 ::
  T_IsSemiringHomomorphism_1366 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_3622 v0
  = coe d_isNearSemiringHomomorphism_1374 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.isRelHomomorphism
d_isRelHomomorphism_3624 ::
  T_IsSemiringHomomorphism_1366 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3624 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe d_isNearSemiringHomomorphism_1374 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringHomomorphism.cong
d_cong_3626 ::
  T_IsSemiringHomomorphism_1366 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3626 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe d_isNearSemiringHomomorphism_1374 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-homo
d_'42''45'homo_3630 ::
  T_IsSemiringIsomorphism_1452 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3630 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_1410
            (coe d_isSemiringMonomorphism_1460 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_3632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3632 v7
du_'42''45'isMagmaHomomorphism_3632 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_3632 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (let v2 = d_isSemiringHomomorphism_1410 (coe v1) in
       coe
         (coe
            du_'42''45'isMagmaHomomorphism_1006
            (coe d_isNearSemiringHomomorphism_1374 (coe v2))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMagmaIsomorphism
d_'42''45'isMagmaIsomorphism_3634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaIsomorphism_240
d_'42''45'isMagmaIsomorphism_3634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaIsomorphism_3634 v7
du_'42''45'isMagmaIsomorphism_3634 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaIsomorphism_240
du_'42''45'isMagmaIsomorphism_3634 v0
  = coe
      du_'42''45'isMagmaIsomorphism_1106
      (coe du_isNearSemiringIsomorphism_1500 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_3636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_3636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_3636 v7
du_'42''45'isMagmaMonomorphism_3636 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_3636 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaMonomorphism_1050
         (coe du_isNearSemiringMonomorphism_1438 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_3638 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_3638 v7
du_'42''45'isMonoidHomomorphism_3638 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_3638 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoidHomomorphism_1396
         (coe d_isSemiringHomomorphism_1410 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMonoidIsomorphism
d_'42''45'isMonoidIsomorphism_3640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
d_'42''45'isMonoidIsomorphism_3640 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidIsomorphism_3640
du_'42''45'isMonoidIsomorphism_3640 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
du_'42''45'isMonoidIsomorphism_3640 v0 v1
  = coe du_'42''45'isMonoidIsomorphism_1508 v1
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_3642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
d_'42''45'isMonoidMonomorphism_3642 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidMonomorphism_3642 v7
du_'42''45'isMonoidMonomorphism_3642 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
du_'42''45'isMonoidMonomorphism_3642 v0
  = coe
      du_'42''45'isMonoidMonomorphism_1446
      (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.homo
d_homo_3644 ::
  T_IsSemiringIsomorphism_1452 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3644 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_1410
                  (coe d_isSemiringMonomorphism_1460 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3646 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3646 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_1410
               (coe d_isSemiringMonomorphism_1460 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3648 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_3648 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_1410
            (coe d_isSemiringMonomorphism_1460 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.+-isMonoidIsomorphism
d_'43''45'isMonoidIsomorphism_3650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
d_'43''45'isMonoidIsomorphism_3650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidIsomorphism_3650 v7
du_'43''45'isMonoidIsomorphism_3650 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidIsomorphism_438
du_'43''45'isMonoidIsomorphism_3650 v0
  = coe
      du_'43''45'isMonoidIsomorphism_1098
      (coe du_isNearSemiringIsomorphism_1500 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_3652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_3652 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_3652 v7
du_'43''45'isMonoidMonomorphism_3652 ::
  T_IsSemiringIsomorphism_1452 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_3652 v0
  = let v1 = d_isSemiringMonomorphism_1460 (coe v0) in
    coe
      (coe
         du_'43''45'isMonoidMonomorphism_1042
         (coe du_isNearSemiringMonomorphism_1438 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.ε-homo
d_ε'45'homo_3654 :: T_IsSemiringIsomorphism_1452 -> AgdaAny
d_ε'45'homo_3654 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_1410
               (coe d_isSemiringMonomorphism_1460 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.1#-homo
d_1'35''45'homo_3656 :: T_IsSemiringIsomorphism_1452 -> AgdaAny
d_1'35''45'homo_3656 v0
  = coe
      d_1'35''45'homo_1376
      (coe
         d_isSemiringHomomorphism_1410
         (coe d_isSemiringMonomorphism_1460 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.injective
d_injective_3658 ::
  T_IsSemiringIsomorphism_1452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3658 v0
  = coe d_injective_1412 (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3660 ::
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_3660 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe
         d_isSemiringHomomorphism_1410
         (coe d_isSemiringMonomorphism_1460 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isNearSemiringIsomorphism
d_isNearSemiringIsomorphism_3662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringIsomorphism_1056
d_isNearSemiringIsomorphism_3662 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isNearSemiringIsomorphism_3662
du_isNearSemiringIsomorphism_3662 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringIsomorphism_1056
du_isNearSemiringIsomorphism_3662 v0 v1
  = coe du_isNearSemiringIsomorphism_1500 v1
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_3664 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringMonomorphism_1012
d_isNearSemiringMonomorphism_3664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiringMonomorphism_3664 v7
du_isNearSemiringMonomorphism_3664 ::
  T_IsSemiringIsomorphism_1452 -> T_IsNearSemiringMonomorphism_1012
du_isNearSemiringMonomorphism_3664 v0
  = coe
      du_isNearSemiringMonomorphism_1438
      (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isRelHomomorphism
d_isRelHomomorphism_3666 ::
  T_IsSemiringIsomorphism_1452 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3666 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_1410
                  (coe d_isSemiringMonomorphism_1460 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_3668 ::
  T_IsSemiringIsomorphism_1452 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_3668 v0
  = coe
      d_isSemiringHomomorphism_1410
      (coe d_isSemiringMonomorphism_1460 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.isSemiringMonomorphism
d_isSemiringMonomorphism_3670 ::
  T_IsSemiringIsomorphism_1452 -> T_IsSemiringMonomorphism_1402
d_isSemiringMonomorphism_3670 v0
  = coe d_isSemiringMonomorphism_1460 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.surjective
d_surjective_3672 ::
  T_IsSemiringIsomorphism_1452 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_3672 v0 = coe d_surjective_1462 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringIsomorphism.cong
d_cong_3674 ::
  T_IsSemiringIsomorphism_1452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3674 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe
                     d_isSemiringHomomorphism_1410
                     (coe d_isSemiringMonomorphism_1460 (coe v0)))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.*-homo
d_'42''45'homo_3678 ::
  T_IsSemiringMonomorphism_1402 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3678 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe d_isSemiringHomomorphism_1410 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_3680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3680 v7
du_'42''45'isMagmaHomomorphism_3680 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_3680 v0
  = let v1 = d_isSemiringHomomorphism_1410 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_1006
         (coe d_isNearSemiringHomomorphism_1374 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.*-isMagmaMonomorphism
d_'42''45'isMagmaMonomorphism_3682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaMonomorphism_214
d_'42''45'isMagmaMonomorphism_3682 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaMonomorphism_3682 v7
du_'42''45'isMagmaMonomorphism_3682 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaMonomorphism_214
du_'42''45'isMagmaMonomorphism_3682 v0
  = coe
      du_'42''45'isMagmaMonomorphism_1050
      (coe du_isNearSemiringMonomorphism_1438 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_3684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_3684 v7
du_'42''45'isMonoidHomomorphism_3684 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_3684 v0
  = coe
      du_'42''45'isMonoidHomomorphism_1396
      (coe d_isSemiringHomomorphism_1410 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.*-isMonoidMonomorphism
d_'42''45'isMonoidMonomorphism_3686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
d_'42''45'isMonoidMonomorphism_3686 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'42''45'isMonoidMonomorphism_3686
du_'42''45'isMonoidMonomorphism_3686 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
du_'42''45'isMonoidMonomorphism_3686 v0 v1
  = coe du_'42''45'isMonoidMonomorphism_1446 v1
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.homo
d_homo_3688 ::
  T_IsSemiringMonomorphism_1402 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3688 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe d_isSemiringHomomorphism_1410 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.isMagmaHomomorphism
d_isMagmaHomomorphism_3690 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3690 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_1410 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3692 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_3692 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe d_isSemiringHomomorphism_1410 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.+-isMonoidMonomorphism
d_'43''45'isMonoidMonomorphism_3694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
d_'43''45'isMonoidMonomorphism_3694 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'43''45'isMonoidMonomorphism_3694 v7
du_'43''45'isMonoidMonomorphism_3694 ::
  T_IsSemiringMonomorphism_1402 -> T_IsMonoidMonomorphism_404
du_'43''45'isMonoidMonomorphism_3694 v0
  = coe
      du_'43''45'isMonoidMonomorphism_1042
      (coe du_isNearSemiringMonomorphism_1438 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.ε-homo
d_ε'45'homo_3696 :: T_IsSemiringMonomorphism_1402 -> AgdaAny
d_ε'45'homo_3696 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_1410 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.1#-homo
d_1'35''45'homo_3698 :: T_IsSemiringMonomorphism_1402 -> AgdaAny
d_1'35''45'homo_3698 v0
  = coe
      d_1'35''45'homo_1376 (coe d_isSemiringHomomorphism_1410 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.injective
d_injective_3700 ::
  T_IsSemiringMonomorphism_1402 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3700 v0 = coe d_injective_1412 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3702 ::
  T_IsSemiringMonomorphism_1402 -> T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_3702 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe d_isSemiringHomomorphism_1410 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.isNearSemiringMonomorphism
d_isNearSemiringMonomorphism_3704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsNearSemiringMonomorphism_1012
d_isNearSemiringMonomorphism_3704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_isNearSemiringMonomorphism_3704
du_isNearSemiringMonomorphism_3704 ::
  (AgdaAny -> AgdaAny) ->
  T_IsSemiringMonomorphism_1402 -> T_IsNearSemiringMonomorphism_1012
du_isNearSemiringMonomorphism_3704 v0 v1
  = coe du_isNearSemiringMonomorphism_1438 v1
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.isRelHomomorphism
d_isRelHomomorphism_3706 ::
  T_IsSemiringMonomorphism_1402 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3706 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe d_isSemiringHomomorphism_1410 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_3708 ::
  T_IsSemiringMonomorphism_1402 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_3708 v0
  = coe d_isSemiringHomomorphism_1410 (coe v0)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms._.IsSemiringMonomorphism.cong
d_cong_3710 ::
  T_IsSemiringMonomorphism_1402 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3710 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe d_isSemiringHomomorphism_1410 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism
d_IsKleeneAlgebraHomomorphism_3714 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsKleeneAlgebraHomomorphism_3714
  = C_constructor_3750 T_IsSemiringHomomorphism_1366
                       (AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism.isSemiringHomomorphism
d_isSemiringHomomorphism_3722 ::
  T_IsKleeneAlgebraHomomorphism_3714 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_3722 v0
  = case coe v0 of
      C_constructor_3750 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism.⋆-homo
d_'8902''45'homo_3724 ::
  T_IsKleeneAlgebraHomomorphism_3714 -> AgdaAny -> AgdaAny
d_'8902''45'homo_3724 v0
  = case coe v0 of
      C_constructor_3750 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.*-homo
d_'42''45'homo_3728 ::
  T_IsKleeneAlgebraHomomorphism_3714 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3728 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe d_isSemiringHomomorphism_3722 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraHomomorphism_3714 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_3730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3730 v7
du_'42''45'isMagmaHomomorphism_3730 ::
  T_IsKleeneAlgebraHomomorphism_3714 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_3730 v0
  = let v1 = d_isSemiringHomomorphism_3722 (coe v0) in
    coe
      (coe
         du_'42''45'isMagmaHomomorphism_1006
         (coe d_isNearSemiringHomomorphism_1374 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraHomomorphism_3714 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_3732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_3732 v7
du_'42''45'isMonoidHomomorphism_3732 ::
  T_IsKleeneAlgebraHomomorphism_3714 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_3732 v0
  = coe
      du_'42''45'isMonoidHomomorphism_1396
      (coe d_isSemiringHomomorphism_3722 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.homo
d_homo_3734 ::
  T_IsKleeneAlgebraHomomorphism_3714 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3734 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe d_isSemiringHomomorphism_3722 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_3736 ::
  T_IsKleeneAlgebraHomomorphism_3714 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3736 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_3722 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3738 ::
  T_IsKleeneAlgebraHomomorphism_3714 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_3738 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe d_isSemiringHomomorphism_3722 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.ε-homo
d_ε'45'homo_3740 :: T_IsKleeneAlgebraHomomorphism_3714 -> AgdaAny
d_ε'45'homo_3740 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe d_isSemiringHomomorphism_3722 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.1#-homo
d_1'35''45'homo_3742 ::
  T_IsKleeneAlgebraHomomorphism_3714 -> AgdaAny
d_1'35''45'homo_3742 v0
  = coe
      d_1'35''45'homo_1376 (coe d_isSemiringHomomorphism_3722 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3744 ::
  T_IsKleeneAlgebraHomomorphism_3714 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_3744 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe d_isSemiringHomomorphism_3722 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.isRelHomomorphism
d_isRelHomomorphism_3746 ::
  T_IsKleeneAlgebraHomomorphism_3714 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3746 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe d_isSemiringHomomorphism_3722 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraHomomorphism._.cong
d_cong_3748 ::
  T_IsKleeneAlgebraHomomorphism_3714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3748 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe d_isSemiringHomomorphism_3722 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism
d_IsKleeneAlgebraMonomorphism_3754 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsKleeneAlgebraMonomorphism_3754
  = C_constructor_3794 T_IsKleeneAlgebraHomomorphism_3714
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism.isKleeneAlgebraHomomorphism
d_isKleeneAlgebraHomomorphism_3762 ::
  T_IsKleeneAlgebraMonomorphism_3754 ->
  T_IsKleeneAlgebraHomomorphism_3714
d_isKleeneAlgebraHomomorphism_3762 v0
  = case coe v0 of
      C_constructor_3794 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism.injective
d_injective_3764 ::
  T_IsKleeneAlgebraMonomorphism_3754 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3764 v0
  = case coe v0 of
      C_constructor_3794 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.*-homo
d_'42''45'homo_3768 ::
  T_IsKleeneAlgebraMonomorphism_3754 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3768 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_3722
            (coe d_isKleeneAlgebraHomomorphism_3762 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3770 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraMonomorphism_3754 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_3770 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3770 v7
du_'42''45'isMagmaHomomorphism_3770 ::
  T_IsKleeneAlgebraMonomorphism_3754 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_3770 v0
  = let v1 = d_isKleeneAlgebraHomomorphism_3762 (coe v0) in
    coe
      (let v2 = d_isSemiringHomomorphism_3722 (coe v1) in
       coe
         (coe
            du_'42''45'isMagmaHomomorphism_1006
            (coe d_isNearSemiringHomomorphism_1374 (coe v2))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraMonomorphism_3754 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_3772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_3772 v7
du_'42''45'isMonoidHomomorphism_3772 ::
  T_IsKleeneAlgebraMonomorphism_3754 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_3772 v0
  = let v1 = d_isKleeneAlgebraHomomorphism_3762 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoidHomomorphism_1396
         (coe d_isSemiringHomomorphism_3722 (coe v1)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.homo
d_homo_3774 ::
  T_IsKleeneAlgebraMonomorphism_3754 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3774 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_3722
                  (coe d_isKleeneAlgebraHomomorphism_3762 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_3776 ::
  T_IsKleeneAlgebraMonomorphism_3754 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3776 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_3722
               (coe d_isKleeneAlgebraHomomorphism_3762 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3778 ::
  T_IsKleeneAlgebraMonomorphism_3754 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_3778 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_3722
            (coe d_isKleeneAlgebraHomomorphism_3762 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.ε-homo
d_ε'45'homo_3780 :: T_IsKleeneAlgebraMonomorphism_3754 -> AgdaAny
d_ε'45'homo_3780 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_3722
               (coe d_isKleeneAlgebraHomomorphism_3762 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.1#-homo
d_1'35''45'homo_3782 ::
  T_IsKleeneAlgebraMonomorphism_3754 -> AgdaAny
d_1'35''45'homo_3782 v0
  = coe
      d_1'35''45'homo_1376
      (coe
         d_isSemiringHomomorphism_3722
         (coe d_isKleeneAlgebraHomomorphism_3762 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3784 ::
  T_IsKleeneAlgebraMonomorphism_3754 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_3784 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe
         d_isSemiringHomomorphism_3722
         (coe d_isKleeneAlgebraHomomorphism_3762 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.isRelHomomorphism
d_isRelHomomorphism_3786 ::
  T_IsKleeneAlgebraMonomorphism_3754 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3786 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_3722
                  (coe d_isKleeneAlgebraHomomorphism_3762 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.isSemiringHomomorphism
d_isSemiringHomomorphism_3788 ::
  T_IsKleeneAlgebraMonomorphism_3754 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_3788 v0
  = coe
      d_isSemiringHomomorphism_3722
      (coe d_isKleeneAlgebraHomomorphism_3762 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.⋆-homo
d_'8902''45'homo_3790 ::
  T_IsKleeneAlgebraMonomorphism_3754 -> AgdaAny -> AgdaAny
d_'8902''45'homo_3790 v0
  = coe
      d_'8902''45'homo_3724
      (coe d_isKleeneAlgebraHomomorphism_3762 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraMonomorphism._.cong
d_cong_3792 ::
  T_IsKleeneAlgebraMonomorphism_3754 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3792 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe
                     d_isSemiringHomomorphism_3722
                     (coe d_isKleeneAlgebraHomomorphism_3762 (coe v0)))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism
d_IsKleeneAlgebraIsomorphism_3798 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsKleeneAlgebraIsomorphism_3798
  = C_constructor_3842 T_IsKleeneAlgebraMonomorphism_3754
                       (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism.isKleeneAlgebraMonomorphism
d_isKleeneAlgebraMonomorphism_3806 ::
  T_IsKleeneAlgebraIsomorphism_3798 ->
  T_IsKleeneAlgebraMonomorphism_3754
d_isKleeneAlgebraMonomorphism_3806 v0
  = case coe v0 of
      C_constructor_3842 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism.surjective
d_surjective_3808 ::
  T_IsKleeneAlgebraIsomorphism_3798 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_3808 v0
  = case coe v0 of
      C_constructor_3842 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.*-homo
d_'42''45'homo_3812 ::
  T_IsKleeneAlgebraIsomorphism_3798 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'homo_3812 v0
  = coe
      d_'42''45'homo_992
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_3722
            (coe
               d_isKleeneAlgebraHomomorphism_3762
               (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.*-isMagmaHomomorphism
d_'42''45'isMagmaHomomorphism_3814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraIsomorphism_3798 -> T_IsMagmaHomomorphism_194
d_'42''45'isMagmaHomomorphism_3814 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagmaHomomorphism_3814 v7
du_'42''45'isMagmaHomomorphism_3814 ::
  T_IsKleeneAlgebraIsomorphism_3798 -> T_IsMagmaHomomorphism_194
du_'42''45'isMagmaHomomorphism_3814 v0
  = let v1 = d_isKleeneAlgebraMonomorphism_3806 (coe v0) in
    coe
      (let v2 = d_isKleeneAlgebraHomomorphism_3762 (coe v1) in
       coe
         (let v3 = d_isSemiringHomomorphism_3722 (coe v2) in
          coe
            (coe
               du_'42''45'isMagmaHomomorphism_1006
               (coe d_isNearSemiringHomomorphism_1374 (coe v3)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.*-isMonoidHomomorphism
d_'42''45'isMonoidHomomorphism_3816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawKleeneAlgebra_440 ->
  (AgdaAny -> AgdaAny) ->
  T_IsKleeneAlgebraIsomorphism_3798 -> T_IsMonoidHomomorphism_380
d_'42''45'isMonoidHomomorphism_3816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMonoidHomomorphism_3816 v7
du_'42''45'isMonoidHomomorphism_3816 ::
  T_IsKleeneAlgebraIsomorphism_3798 -> T_IsMonoidHomomorphism_380
du_'42''45'isMonoidHomomorphism_3816 v0
  = let v1 = d_isKleeneAlgebraMonomorphism_3806 (coe v0) in
    coe
      (let v2 = d_isKleeneAlgebraHomomorphism_3762 (coe v1) in
       coe
         (coe
            du_'42''45'isMonoidHomomorphism_1396
            (coe d_isSemiringHomomorphism_3722 (coe v2))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.homo
d_homo_3818 ::
  T_IsKleeneAlgebraIsomorphism_3798 -> AgdaAny -> AgdaAny -> AgdaAny
d_homo_3818 v0
  = coe
      d_homo_204
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_3722
                  (coe
                     d_isKleeneAlgebraHomomorphism_3762
                     (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0)))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.isMagmaHomomorphism
d_isMagmaHomomorphism_3820 ::
  T_IsKleeneAlgebraIsomorphism_3798 -> T_IsMagmaHomomorphism_194
d_isMagmaHomomorphism_3820 v0
  = coe
      d_isMagmaHomomorphism_388
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_3722
               (coe
                  d_isKleeneAlgebraHomomorphism_3762
                  (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.+-isMonoidHomomorphism
d_'43''45'isMonoidHomomorphism_3822 ::
  T_IsKleeneAlgebraIsomorphism_3798 -> T_IsMonoidHomomorphism_380
d_'43''45'isMonoidHomomorphism_3822 v0
  = coe
      d_'43''45'isMonoidHomomorphism_990
      (coe
         d_isNearSemiringHomomorphism_1374
         (coe
            d_isSemiringHomomorphism_3722
            (coe
               d_isKleeneAlgebraHomomorphism_3762
               (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0)))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.ε-homo
d_ε'45'homo_3824 :: T_IsKleeneAlgebraIsomorphism_3798 -> AgdaAny
d_ε'45'homo_3824 v0
  = coe
      d_ε'45'homo_390
      (coe
         d_'43''45'isMonoidHomomorphism_990
         (coe
            d_isNearSemiringHomomorphism_1374
            (coe
               d_isSemiringHomomorphism_3722
               (coe
                  d_isKleeneAlgebraHomomorphism_3762
                  (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.1#-homo
d_1'35''45'homo_3826 ::
  T_IsKleeneAlgebraIsomorphism_3798 -> AgdaAny
d_1'35''45'homo_3826 v0
  = coe
      d_1'35''45'homo_1376
      (coe
         d_isSemiringHomomorphism_3722
         (coe
            d_isKleeneAlgebraHomomorphism_3762
            (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.injective
d_injective_3828 ::
  T_IsKleeneAlgebraIsomorphism_3798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_3828 v0
  = coe
      d_injective_3764 (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.isKleeneAlgebraHomomorphism
d_isKleeneAlgebraHomomorphism_3830 ::
  T_IsKleeneAlgebraIsomorphism_3798 ->
  T_IsKleeneAlgebraHomomorphism_3714
d_isKleeneAlgebraHomomorphism_3830 v0
  = coe
      d_isKleeneAlgebraHomomorphism_3762
      (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.isNearSemiringHomomorphism
d_isNearSemiringHomomorphism_3832 ::
  T_IsKleeneAlgebraIsomorphism_3798 ->
  T_IsNearSemiringHomomorphism_982
d_isNearSemiringHomomorphism_3832 v0
  = coe
      d_isNearSemiringHomomorphism_1374
      (coe
         d_isSemiringHomomorphism_3722
         (coe
            d_isKleeneAlgebraHomomorphism_3762
            (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.isRelHomomorphism
d_isRelHomomorphism_3834 ::
  T_IsKleeneAlgebraIsomorphism_3798 ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_isRelHomomorphism_3834 v0
  = coe
      d_isRelHomomorphism_202
      (coe
         d_isMagmaHomomorphism_388
         (coe
            d_'43''45'isMonoidHomomorphism_990
            (coe
               d_isNearSemiringHomomorphism_1374
               (coe
                  d_isSemiringHomomorphism_3722
                  (coe
                     d_isKleeneAlgebraHomomorphism_3762
                     (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0)))))))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.isSemiringHomomorphism
d_isSemiringHomomorphism_3836 ::
  T_IsKleeneAlgebraIsomorphism_3798 -> T_IsSemiringHomomorphism_1366
d_isSemiringHomomorphism_3836 v0
  = coe
      d_isSemiringHomomorphism_3722
      (coe
         d_isKleeneAlgebraHomomorphism_3762
         (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.⋆-homo
d_'8902''45'homo_3838 ::
  T_IsKleeneAlgebraIsomorphism_3798 -> AgdaAny -> AgdaAny
d_'8902''45'homo_3838 v0
  = coe
      d_'8902''45'homo_3724
      (coe
         d_isKleeneAlgebraHomomorphism_3762
         (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0)))
-- Algebra.Morphism.Structures.KleeneAlgebraMorphisms.IsKleeneAlgebraIsomorphism._.cong
d_cong_3840 ::
  T_IsKleeneAlgebraIsomorphism_3798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_3840 v0
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
      (coe
         d_isRelHomomorphism_202
         (coe
            d_isMagmaHomomorphism_388
            (coe
               d_'43''45'isMonoidHomomorphism_990
               (coe
                  d_isNearSemiringHomomorphism_1374
                  (coe
                     d_isSemiringHomomorphism_3722
                     (coe
                        d_isKleeneAlgebraHomomorphism_3762
                        (coe d_isKleeneAlgebraMonomorphism_3806 (coe v0))))))))
