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

module MAlonzo.Code.Algebra.Structures where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Consequences.Setoid
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Structures._._DistributesOver_
d__DistributesOver__16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver__16 = erased
-- Algebra.Structures._._DistributesOverʳ_
d__DistributesOver'691'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'691'__18 = erased
-- Algebra.Structures._._DistributesOverˡ_
d__DistributesOver'737'__20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'737'__20 = erased
-- Algebra.Structures._.AlmostLeftCancellative
d_AlmostLeftCancellative_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_AlmostLeftCancellative_30 = erased
-- Algebra.Structures._.AlmostRightCancellative
d_AlmostRightCancellative_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_AlmostRightCancellative_32 = erased
-- Algebra.Structures._.Alternative
d_Alternative_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Alternative_34 = erased
-- Algebra.Structures._.Associative
d_Associative_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Associative_36 = erased
-- Algebra.Structures._.Commutative
d_Commutative_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Commutative_40 = erased
-- Algebra.Structures._.Congruent₁
d_Congruent'8321'_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d_Congruent'8321'_42 = erased
-- Algebra.Structures._.Congruent₂
d_Congruent'8322'_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Congruent'8322'_44 = erased
-- Algebra.Structures._.Flexible
d_Flexible_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Flexible_48 = erased
-- Algebra.Structures._.Idempotent
d_Idempotent_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Idempotent_50 = erased
-- Algebra.Structures._.Identical
d_Identical_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Identical_54 = erased
-- Algebra.Structures._.Identity
d_Identity_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Identity_56 = erased
-- Algebra.Structures._.Inverse
d_Inverse_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Inverse_60 = erased
-- Algebra.Structures._.LeftAlternative
d_LeftAlternative_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftAlternative_66 = erased
-- Algebra.Structures._.LeftBol
d_LeftBol_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftBol_68 = erased
-- Algebra.Structures._.LeftCongruent
d_LeftCongruent_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftCongruent_72 = erased
-- Algebra.Structures._.LeftDivides
d_LeftDivides_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides_76 = erased
-- Algebra.Structures._.LeftDividesʳ
d_LeftDivides'691'_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides'691'_78 = erased
-- Algebra.Structures._.LeftDividesˡ
d_LeftDivides'737'_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides'737'_80 = erased
-- Algebra.Structures._.LeftIdentity
d_LeftIdentity_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftIdentity_82 = erased
-- Algebra.Structures._.LeftInverse
d_LeftInverse_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftInverse_84 = erased
-- Algebra.Structures._.LeftSemimedial
d_LeftSemimedial_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftSemimedial_88 = erased
-- Algebra.Structures._.LeftZero
d_LeftZero_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftZero_90 = erased
-- Algebra.Structures._.Medial
d_Medial_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Medial_92 = erased
-- Algebra.Structures._.MiddleBol
d_MiddleBol_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_MiddleBol_94 = erased
-- Algebra.Structures._.RightAlternative
d_RightAlternative_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightAlternative_96 = erased
-- Algebra.Structures._.RightBol
d_RightBol_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightBol_98 = erased
-- Algebra.Structures._.RightCongruent
d_RightCongruent_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightCongruent_102 = erased
-- Algebra.Structures._.RightDivides
d_RightDivides_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides_106 = erased
-- Algebra.Structures._.RightDividesʳ
d_RightDivides'691'_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides'691'_108 = erased
-- Algebra.Structures._.RightDividesˡ
d_RightDivides'737'_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides'737'_110 = erased
-- Algebra.Structures._.RightIdentity
d_RightIdentity_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightIdentity_112 = erased
-- Algebra.Structures._.RightInverse
d_RightInverse_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightInverse_114 = erased
-- Algebra.Structures._.RightSemimedial
d_RightSemimedial_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightSemimedial_118 = erased
-- Algebra.Structures._.RightZero
d_RightZero_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightZero_120 = erased
-- Algebra.Structures._.Selective
d_Selective_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Selective_122 = erased
-- Algebra.Structures._.Semimedial
d_Semimedial_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Semimedial_126 = erased
-- Algebra.Structures._.StarDestructive
d_StarDestructive_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarDestructive_128 = erased
-- Algebra.Structures._.StarExpansive
d_StarExpansive_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarExpansive_130 = erased
-- Algebra.Structures._.StarLeftDestructive
d_StarLeftDestructive_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarLeftDestructive_132 = erased
-- Algebra.Structures._.StarLeftExpansive
d_StarLeftExpansive_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarLeftExpansive_134 = erased
-- Algebra.Structures._.StarRightDestructive
d_StarRightDestructive_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarRightDestructive_136 = erased
-- Algebra.Structures._.StarRightExpansive
d_StarRightExpansive_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarRightExpansive_138 = erased
-- Algebra.Structures._.Zero
d_Zero_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Zero_140 = erased
-- Algebra.Structures.IsSuccessorSet
d_IsSuccessorSet_146 a0 a1 a2 a3 a4 a5 = ()
data T_IsSuccessorSet_146
  = C_constructor_174 MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsSuccessorSet.isEquivalence
d_isEquivalence_156 ::
  T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_156 v0
  = case coe v0 of
      C_constructor_174 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSuccessorSet.suc#-cong
d_suc'35''45'cong_158 ::
  T_IsSuccessorSet_146 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_suc'35''45'cong_158 v0
  = case coe v0 of
      C_constructor_174 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSuccessorSet._.isPartialEquivalence
d_isPartialEquivalence_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_162 v6
du_isPartialEquivalence_162 ::
  T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_162 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe d_isEquivalence_156 (coe v0))
-- Algebra.Structures.IsSuccessorSet._.refl
d_refl_164 :: T_IsSuccessorSet_146 -> AgdaAny -> AgdaAny
d_refl_164 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_156 (coe v0))
-- Algebra.Structures.IsSuccessorSet._.reflexive
d_reflexive_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSuccessorSet_146 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_166 v6
du_reflexive_166 ::
  T_IsSuccessorSet_146 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_166 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
      (coe d_isEquivalence_156 (coe v0)) v1
-- Algebra.Structures.IsSuccessorSet._.sym
d_sym_168 ::
  T_IsSuccessorSet_146 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_168 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_156 (coe v0))
-- Algebra.Structures.IsSuccessorSet._.trans
d_trans_170 ::
  T_IsSuccessorSet_146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_170 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_156 (coe v0))
-- Algebra.Structures.IsSuccessorSet.setoid
d_setoid_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_172 v6
du_setoid_172 ::
  T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_172 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (d_isEquivalence_156 (coe v0))
-- Algebra.Structures.IsMagma
d_IsMagma_178 a0 a1 a2 a3 a4 = ()
data T_IsMagma_178
  = C_constructor_210 MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
                      (AgdaAny ->
                       AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsMagma.isEquivalence
d_isEquivalence_186 ::
  T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_186 v0
  = case coe v0 of
      C_constructor_210 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMagma.∙-cong
d_'8729''45'cong_188 ::
  T_IsMagma_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_188 v0
  = case coe v0 of
      C_constructor_210 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMagma._.isPartialEquivalence
d_isPartialEquivalence_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_192 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_192 v5
du_isPartialEquivalence_192 ::
  T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe d_isEquivalence_186 (coe v0))
-- Algebra.Structures.IsMagma._.refl
d_refl_194 :: T_IsMagma_178 -> AgdaAny -> AgdaAny
d_refl_194 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe v0))
-- Algebra.Structures.IsMagma._.reflexive
d_reflexive_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMagma_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_196 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_196 v5
du_reflexive_196 ::
  T_IsMagma_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_196 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
      (coe d_isEquivalence_186 (coe v0)) v1
-- Algebra.Structures.IsMagma._.sym
d_sym_198 ::
  T_IsMagma_178 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_198 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe v0))
-- Algebra.Structures.IsMagma._.trans
d_trans_200 ::
  T_IsMagma_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_200 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe v0))
-- Algebra.Structures.IsMagma.setoid
d_setoid_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMagma_178 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_202 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_202 v5
du_setoid_202 ::
  T_IsMagma_178 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_202 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (d_isEquivalence_186 (coe v0))
-- Algebra.Structures.IsMagma._.∙-congʳ
d_'8729''45'cong'691'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMagma_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_206 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_206 v5
du_'8729''45'cong'691'_206 ::
  T_IsMagma_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_206 v0
  = let v1 = coe du_setoid_202 (coe v0) in
    coe
      (let v2 = d_'8729''45'cong_188 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
            (coe v2)
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v1)))))
-- Algebra.Structures.IsMagma._.∙-congˡ
d_'8729''45'cong'737'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMagma_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_208 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_208 v5
du_'8729''45'cong'737'_208 ::
  T_IsMagma_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_208 v0
  = let v1 = coe du_setoid_202 (coe v0) in
    coe
      (let v2 = d_'8729''45'cong_188 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
            (coe v2)
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v1)))))
-- Algebra.Structures.IsCommutativeMagma
d_IsCommutativeMagma_214 a0 a1 a2 a3 a4 = ()
data T_IsCommutativeMagma_214
  = C_constructor_248 T_IsMagma_178 (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeMagma.isMagma
d_isMagma_222 :: T_IsCommutativeMagma_214 -> T_IsMagma_178
d_isMagma_222 v0
  = case coe v0 of
      C_constructor_248 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeMagma.comm
d_comm_224 ::
  T_IsCommutativeMagma_214 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_224 v0
  = case coe v0 of
      C_constructor_248 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeMagma._.isEquivalence
d_isEquivalence_228 ::
  T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_228 v0
  = coe d_isEquivalence_186 (coe d_isMagma_222 (coe v0))
-- Algebra.Structures.IsCommutativeMagma._.isPartialEquivalence
d_isPartialEquivalence_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_230 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_230 v5
du_isPartialEquivalence_230 ::
  T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_230 v0
  = let v1 = d_isMagma_222 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_186 (coe v1)))
-- Algebra.Structures.IsCommutativeMagma._.refl
d_refl_232 :: T_IsCommutativeMagma_214 -> AgdaAny -> AgdaAny
d_refl_232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe d_isMagma_222 (coe v0)))
-- Algebra.Structures.IsCommutativeMagma._.reflexive
d_reflexive_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeMagma_214 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_234 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_234 v5
du_reflexive_234 ::
  T_IsCommutativeMagma_214 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_234 v0
  = let v1 = d_isMagma_222 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_186 (coe v1)) v2)
-- Algebra.Structures.IsCommutativeMagma._.setoid
d_setoid_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_236 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_236 v5
du_setoid_236 ::
  T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_236 v0 = coe du_setoid_202 (coe d_isMagma_222 (coe v0))
-- Algebra.Structures.IsCommutativeMagma._.sym
d_sym_238 ::
  T_IsCommutativeMagma_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_238 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe d_isMagma_222 (coe v0)))
-- Algebra.Structures.IsCommutativeMagma._.trans
d_trans_240 ::
  T_IsCommutativeMagma_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_240 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe d_isMagma_222 (coe v0)))
-- Algebra.Structures.IsCommutativeMagma._.∙-cong
d_'8729''45'cong_242 ::
  T_IsCommutativeMagma_214 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_242 v0
  = coe d_'8729''45'cong_188 (coe d_isMagma_222 (coe v0))
-- Algebra.Structures.IsCommutativeMagma._.∙-congʳ
d_'8729''45'cong'691'_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeMagma_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_244 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_244 v5
du_'8729''45'cong'691'_244 ::
  T_IsCommutativeMagma_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_244 v0
  = let v1 = d_isMagma_222 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsCommutativeMagma._.∙-congˡ
d_'8729''45'cong'737'_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeMagma_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_246 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_246 v5
du_'8729''45'cong'737'_246 ::
  T_IsCommutativeMagma_214 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_246 v0
  = let v1 = d_isMagma_222 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsIdempotentMagma
d_IsIdempotentMagma_252 a0 a1 a2 a3 a4 = ()
data T_IsIdempotentMagma_252
  = C_constructor_286 T_IsMagma_178 (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsIdempotentMagma.isMagma
d_isMagma_260 :: T_IsIdempotentMagma_252 -> T_IsMagma_178
d_isMagma_260 v0
  = case coe v0 of
      C_constructor_286 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentMagma.idem
d_idem_262 :: T_IsIdempotentMagma_252 -> AgdaAny -> AgdaAny
d_idem_262 v0
  = case coe v0 of
      C_constructor_286 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentMagma._.isEquivalence
d_isEquivalence_266 ::
  T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_266 v0
  = coe d_isEquivalence_186 (coe d_isMagma_260 (coe v0))
-- Algebra.Structures.IsIdempotentMagma._.isPartialEquivalence
d_isPartialEquivalence_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_268 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_268 v5
du_isPartialEquivalence_268 ::
  T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_268 v0
  = let v1 = d_isMagma_260 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_186 (coe v1)))
-- Algebra.Structures.IsIdempotentMagma._.refl
d_refl_270 :: T_IsIdempotentMagma_252 -> AgdaAny -> AgdaAny
d_refl_270 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe d_isMagma_260 (coe v0)))
-- Algebra.Structures.IsIdempotentMagma._.reflexive
d_reflexive_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsIdempotentMagma_252 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_272 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_272 v5
du_reflexive_272 ::
  T_IsIdempotentMagma_252 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_272 v0
  = let v1 = d_isMagma_260 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_186 (coe v1)) v2)
-- Algebra.Structures.IsIdempotentMagma._.setoid
d_setoid_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_274 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_274 v5
du_setoid_274 ::
  T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_274 v0 = coe du_setoid_202 (coe d_isMagma_260 (coe v0))
-- Algebra.Structures.IsIdempotentMagma._.sym
d_sym_276 ::
  T_IsIdempotentMagma_252 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_276 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe d_isMagma_260 (coe v0)))
-- Algebra.Structures.IsIdempotentMagma._.trans
d_trans_278 ::
  T_IsIdempotentMagma_252 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_278 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe d_isMagma_260 (coe v0)))
-- Algebra.Structures.IsIdempotentMagma._.∙-cong
d_'8729''45'cong_280 ::
  T_IsIdempotentMagma_252 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_280 v0
  = coe d_'8729''45'cong_188 (coe d_isMagma_260 (coe v0))
-- Algebra.Structures.IsIdempotentMagma._.∙-congʳ
d_'8729''45'cong'691'_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsIdempotentMagma_252 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_282 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_282 v5
du_'8729''45'cong'691'_282 ::
  T_IsIdempotentMagma_252 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_282 v0
  = let v1 = d_isMagma_260 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsIdempotentMagma._.∙-congˡ
d_'8729''45'cong'737'_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsIdempotentMagma_252 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_284 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_284 v5
du_'8729''45'cong'737'_284 ::
  T_IsIdempotentMagma_252 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_284 v0
  = let v1 = d_isMagma_260 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsAlternativeMagma
d_IsAlternativeMagma_290 a0 a1 a2 a3 a4 = ()
data T_IsAlternativeMagma_290
  = C_constructor_328 T_IsMagma_178
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsAlternativeMagma.isMagma
d_isMagma_298 :: T_IsAlternativeMagma_290 -> T_IsMagma_178
d_isMagma_298 v0
  = case coe v0 of
      C_constructor_328 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsAlternativeMagma.alter
d_alter_300 ::
  T_IsAlternativeMagma_290 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alter_300 v0
  = case coe v0 of
      C_constructor_328 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsAlternativeMagma._.isEquivalence
d_isEquivalence_304 ::
  T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_304 v0
  = coe d_isEquivalence_186 (coe d_isMagma_298 (coe v0))
-- Algebra.Structures.IsAlternativeMagma._.isPartialEquivalence
d_isPartialEquivalence_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_306 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_306 v5
du_isPartialEquivalence_306 ::
  T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_306 v0
  = let v1 = d_isMagma_298 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_186 (coe v1)))
-- Algebra.Structures.IsAlternativeMagma._.refl
d_refl_308 :: T_IsAlternativeMagma_290 -> AgdaAny -> AgdaAny
d_refl_308 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe d_isMagma_298 (coe v0)))
-- Algebra.Structures.IsAlternativeMagma._.reflexive
d_reflexive_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_290 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_310 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_310 v5
du_reflexive_310 ::
  T_IsAlternativeMagma_290 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_310 v0
  = let v1 = d_isMagma_298 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_186 (coe v1)) v2)
-- Algebra.Structures.IsAlternativeMagma._.setoid
d_setoid_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_312 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_312 v5
du_setoid_312 ::
  T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_312 v0 = coe du_setoid_202 (coe d_isMagma_298 (coe v0))
-- Algebra.Structures.IsAlternativeMagma._.sym
d_sym_314 ::
  T_IsAlternativeMagma_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_314 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe d_isMagma_298 (coe v0)))
-- Algebra.Structures.IsAlternativeMagma._.trans
d_trans_316 ::
  T_IsAlternativeMagma_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_316 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe d_isMagma_298 (coe v0)))
-- Algebra.Structures.IsAlternativeMagma._.∙-cong
d_'8729''45'cong_318 ::
  T_IsAlternativeMagma_290 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_318 v0
  = coe d_'8729''45'cong_188 (coe d_isMagma_298 (coe v0))
-- Algebra.Structures.IsAlternativeMagma._.∙-congʳ
d_'8729''45'cong'691'_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_320 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_320 v5
du_'8729''45'cong'691'_320 ::
  T_IsAlternativeMagma_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_320 v0
  = let v1 = d_isMagma_298 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsAlternativeMagma._.∙-congˡ
d_'8729''45'cong'737'_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_322 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_322 v5
du_'8729''45'cong'737'_322 ::
  T_IsAlternativeMagma_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_322 v0
  = let v1 = d_isMagma_298 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsAlternativeMagma.alternativeˡ
d_alternative'737'_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_290 -> AgdaAny -> AgdaAny -> AgdaAny
d_alternative'737'_324 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_alternative'737'_324 v5
du_alternative'737'_324 ::
  T_IsAlternativeMagma_290 -> AgdaAny -> AgdaAny -> AgdaAny
du_alternative'737'_324 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_alter_300 (coe v0))
-- Algebra.Structures.IsAlternativeMagma.alternativeʳ
d_alternative'691'_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_290 -> AgdaAny -> AgdaAny -> AgdaAny
d_alternative'691'_326 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_alternative'691'_326 v5
du_alternative'691'_326 ::
  T_IsAlternativeMagma_290 -> AgdaAny -> AgdaAny -> AgdaAny
du_alternative'691'_326 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_alter_300 (coe v0))
-- Algebra.Structures.IsFlexibleMagma
d_IsFlexibleMagma_332 a0 a1 a2 a3 a4 = ()
data T_IsFlexibleMagma_332
  = C_constructor_366 T_IsMagma_178 (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsFlexibleMagma.isMagma
d_isMagma_340 :: T_IsFlexibleMagma_332 -> T_IsMagma_178
d_isMagma_340 v0
  = case coe v0 of
      C_constructor_366 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsFlexibleMagma.flex
d_flex_342 ::
  T_IsFlexibleMagma_332 -> AgdaAny -> AgdaAny -> AgdaAny
d_flex_342 v0
  = case coe v0 of
      C_constructor_366 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsFlexibleMagma._.isEquivalence
d_isEquivalence_346 ::
  T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_346 v0
  = coe d_isEquivalence_186 (coe d_isMagma_340 (coe v0))
-- Algebra.Structures.IsFlexibleMagma._.isPartialEquivalence
d_isPartialEquivalence_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_348 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_348 v5
du_isPartialEquivalence_348 ::
  T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_348 v0
  = let v1 = d_isMagma_340 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_186 (coe v1)))
-- Algebra.Structures.IsFlexibleMagma._.refl
d_refl_350 :: T_IsFlexibleMagma_332 -> AgdaAny -> AgdaAny
d_refl_350 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe d_isMagma_340 (coe v0)))
-- Algebra.Structures.IsFlexibleMagma._.reflexive
d_reflexive_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsFlexibleMagma_332 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_352 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_352 v5
du_reflexive_352 ::
  T_IsFlexibleMagma_332 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_352 v0
  = let v1 = d_isMagma_340 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_186 (coe v1)) v2)
-- Algebra.Structures.IsFlexibleMagma._.setoid
d_setoid_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_354 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_354 v5
du_setoid_354 ::
  T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_354 v0 = coe du_setoid_202 (coe d_isMagma_340 (coe v0))
-- Algebra.Structures.IsFlexibleMagma._.sym
d_sym_356 ::
  T_IsFlexibleMagma_332 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_356 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe d_isMagma_340 (coe v0)))
-- Algebra.Structures.IsFlexibleMagma._.trans
d_trans_358 ::
  T_IsFlexibleMagma_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_358 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe d_isMagma_340 (coe v0)))
-- Algebra.Structures.IsFlexibleMagma._.∙-cong
d_'8729''45'cong_360 ::
  T_IsFlexibleMagma_332 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_360 v0
  = coe d_'8729''45'cong_188 (coe d_isMagma_340 (coe v0))
-- Algebra.Structures.IsFlexibleMagma._.∙-congʳ
d_'8729''45'cong'691'_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsFlexibleMagma_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_362 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_362 v5
du_'8729''45'cong'691'_362 ::
  T_IsFlexibleMagma_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_362 v0
  = let v1 = d_isMagma_340 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsFlexibleMagma._.∙-congˡ
d_'8729''45'cong'737'_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsFlexibleMagma_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_364 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_364 v5
du_'8729''45'cong'737'_364 ::
  T_IsFlexibleMagma_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_364 v0
  = let v1 = d_isMagma_340 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsMedialMagma
d_IsMedialMagma_370 a0 a1 a2 a3 a4 = ()
data T_IsMedialMagma_370
  = C_constructor_404 T_IsMagma_178
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsMedialMagma.isMagma
d_isMagma_378 :: T_IsMedialMagma_370 -> T_IsMagma_178
d_isMagma_378 v0
  = case coe v0 of
      C_constructor_404 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMedialMagma.medial
d_medial_380 ::
  T_IsMedialMagma_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_medial_380 v0
  = case coe v0 of
      C_constructor_404 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMedialMagma._.isEquivalence
d_isEquivalence_384 ::
  T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_384 v0
  = coe d_isEquivalence_186 (coe d_isMagma_378 (coe v0))
-- Algebra.Structures.IsMedialMagma._.isPartialEquivalence
d_isPartialEquivalence_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_386 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_386 v5
du_isPartialEquivalence_386 ::
  T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_386 v0
  = let v1 = d_isMagma_378 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_186 (coe v1)))
-- Algebra.Structures.IsMedialMagma._.refl
d_refl_388 :: T_IsMedialMagma_370 -> AgdaAny -> AgdaAny
d_refl_388 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe d_isMagma_378 (coe v0)))
-- Algebra.Structures.IsMedialMagma._.reflexive
d_reflexive_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMedialMagma_370 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_390 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_390 v5
du_reflexive_390 ::
  T_IsMedialMagma_370 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_390 v0
  = let v1 = d_isMagma_378 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_186 (coe v1)) v2)
-- Algebra.Structures.IsMedialMagma._.setoid
d_setoid_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_392 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_392 v5
du_setoid_392 ::
  T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_392 v0 = coe du_setoid_202 (coe d_isMagma_378 (coe v0))
-- Algebra.Structures.IsMedialMagma._.sym
d_sym_394 ::
  T_IsMedialMagma_370 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_394 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe d_isMagma_378 (coe v0)))
-- Algebra.Structures.IsMedialMagma._.trans
d_trans_396 ::
  T_IsMedialMagma_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_396 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe d_isMagma_378 (coe v0)))
-- Algebra.Structures.IsMedialMagma._.∙-cong
d_'8729''45'cong_398 ::
  T_IsMedialMagma_370 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_398 v0
  = coe d_'8729''45'cong_188 (coe d_isMagma_378 (coe v0))
-- Algebra.Structures.IsMedialMagma._.∙-congʳ
d_'8729''45'cong'691'_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMedialMagma_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_400 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_400 v5
du_'8729''45'cong'691'_400 ::
  T_IsMedialMagma_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_400 v0
  = let v1 = d_isMagma_378 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsMedialMagma._.∙-congˡ
d_'8729''45'cong'737'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMedialMagma_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_402 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_402 v5
du_'8729''45'cong'737'_402 ::
  T_IsMedialMagma_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_402 v0
  = let v1 = d_isMagma_378 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsSemimedialMagma
d_IsSemimedialMagma_408 a0 a1 a2 a3 a4 = ()
data T_IsSemimedialMagma_408
  = C_constructor_446 T_IsMagma_178
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsSemimedialMagma.isMagma
d_isMagma_416 :: T_IsSemimedialMagma_408 -> T_IsMagma_178
d_isMagma_416 v0
  = case coe v0 of
      C_constructor_446 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemimedialMagma.semiMedial
d_semiMedial_418 ::
  T_IsSemimedialMagma_408 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_semiMedial_418 v0
  = case coe v0 of
      C_constructor_446 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemimedialMagma._.isEquivalence
d_isEquivalence_422 ::
  T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_422 v0
  = coe d_isEquivalence_186 (coe d_isMagma_416 (coe v0))
-- Algebra.Structures.IsSemimedialMagma._.isPartialEquivalence
d_isPartialEquivalence_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_424 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_424 v5
du_isPartialEquivalence_424 ::
  T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_424 v0
  = let v1 = d_isMagma_416 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_186 (coe v1)))
-- Algebra.Structures.IsSemimedialMagma._.refl
d_refl_426 :: T_IsSemimedialMagma_408 -> AgdaAny -> AgdaAny
d_refl_426 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe d_isMagma_416 (coe v0)))
-- Algebra.Structures.IsSemimedialMagma._.reflexive
d_reflexive_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_428 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_428 v5
du_reflexive_428 ::
  T_IsSemimedialMagma_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_428 v0
  = let v1 = d_isMagma_416 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_186 (coe v1)) v2)
-- Algebra.Structures.IsSemimedialMagma._.setoid
d_setoid_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_430 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_430 v5
du_setoid_430 ::
  T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_430 v0 = coe du_setoid_202 (coe d_isMagma_416 (coe v0))
-- Algebra.Structures.IsSemimedialMagma._.sym
d_sym_432 ::
  T_IsSemimedialMagma_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_432 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe d_isMagma_416 (coe v0)))
-- Algebra.Structures.IsSemimedialMagma._.trans
d_trans_434 ::
  T_IsSemimedialMagma_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_434 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe d_isMagma_416 (coe v0)))
-- Algebra.Structures.IsSemimedialMagma._.∙-cong
d_'8729''45'cong_436 ::
  T_IsSemimedialMagma_408 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_436 v0
  = coe d_'8729''45'cong_188 (coe d_isMagma_416 (coe v0))
-- Algebra.Structures.IsSemimedialMagma._.∙-congʳ
d_'8729''45'cong'691'_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_438 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_438 v5
du_'8729''45'cong'691'_438 ::
  T_IsSemimedialMagma_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_438 v0
  = let v1 = d_isMagma_416 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsSemimedialMagma._.∙-congˡ
d_'8729''45'cong'737'_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_440 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_440 v5
du_'8729''45'cong'737'_440 ::
  T_IsSemimedialMagma_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_440 v0
  = let v1 = d_isMagma_416 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsSemimedialMagma.semimedialˡ
d_semimedial'737'_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_semimedial'737'_442 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_semimedial'737'_442 v5
du_semimedial'737'_442 ::
  T_IsSemimedialMagma_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_semimedial'737'_442 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_semiMedial_418 (coe v0))
-- Algebra.Structures.IsSemimedialMagma.semimedialʳ
d_semimedial'691'_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_semimedial'691'_444 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_semimedial'691'_444 v5
du_semimedial'691'_444 ::
  T_IsSemimedialMagma_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_semimedial'691'_444 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_semiMedial_418 (coe v0))
-- Algebra.Structures.IsSelectiveMagma
d_IsSelectiveMagma_450 a0 a1 a2 a3 a4 = ()
data T_IsSelectiveMagma_450
  = C_constructor_484 T_IsMagma_178
                      (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Algebra.Structures.IsSelectiveMagma.isMagma
d_isMagma_458 :: T_IsSelectiveMagma_450 -> T_IsMagma_178
d_isMagma_458 v0
  = case coe v0 of
      C_constructor_484 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSelectiveMagma.sel
d_sel_460 ::
  T_IsSelectiveMagma_450 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_460 v0
  = case coe v0 of
      C_constructor_484 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSelectiveMagma._.isEquivalence
d_isEquivalence_464 ::
  T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_464 v0
  = coe d_isEquivalence_186 (coe d_isMagma_458 (coe v0))
-- Algebra.Structures.IsSelectiveMagma._.isPartialEquivalence
d_isPartialEquivalence_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_466 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_466 v5
du_isPartialEquivalence_466 ::
  T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_466 v0
  = let v1 = d_isMagma_458 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_186 (coe v1)))
-- Algebra.Structures.IsSelectiveMagma._.refl
d_refl_468 :: T_IsSelectiveMagma_450 -> AgdaAny -> AgdaAny
d_refl_468 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe d_isMagma_458 (coe v0)))
-- Algebra.Structures.IsSelectiveMagma._.reflexive
d_reflexive_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSelectiveMagma_450 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_470 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_470 v5
du_reflexive_470 ::
  T_IsSelectiveMagma_450 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_470 v0
  = let v1 = d_isMagma_458 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_186 (coe v1)) v2)
-- Algebra.Structures.IsSelectiveMagma._.setoid
d_setoid_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_472 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_472 v5
du_setoid_472 ::
  T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_472 v0 = coe du_setoid_202 (coe d_isMagma_458 (coe v0))
-- Algebra.Structures.IsSelectiveMagma._.sym
d_sym_474 ::
  T_IsSelectiveMagma_450 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_474 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe d_isMagma_458 (coe v0)))
-- Algebra.Structures.IsSelectiveMagma._.trans
d_trans_476 ::
  T_IsSelectiveMagma_450 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_476 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe d_isMagma_458 (coe v0)))
-- Algebra.Structures.IsSelectiveMagma._.∙-cong
d_'8729''45'cong_478 ::
  T_IsSelectiveMagma_450 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_478 v0
  = coe d_'8729''45'cong_188 (coe d_isMagma_458 (coe v0))
-- Algebra.Structures.IsSelectiveMagma._.∙-congʳ
d_'8729''45'cong'691'_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSelectiveMagma_450 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_480 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_480 v5
du_'8729''45'cong'691'_480 ::
  T_IsSelectiveMagma_450 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_480 v0
  = let v1 = d_isMagma_458 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsSelectiveMagma._.∙-congˡ
d_'8729''45'cong'737'_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSelectiveMagma_450 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_482 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_482 v5
du_'8729''45'cong'737'_482 ::
  T_IsSelectiveMagma_450 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_482 v0
  = let v1 = d_isMagma_458 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsSemigroup
d_IsSemigroup_488 a0 a1 a2 a3 a4 = ()
data T_IsSemigroup_488
  = C_constructor_522 T_IsMagma_178
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsSemigroup.isMagma
d_isMagma_496 :: T_IsSemigroup_488 -> T_IsMagma_178
d_isMagma_496 v0
  = case coe v0 of
      C_constructor_522 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemigroup.assoc
d_assoc_498 ::
  T_IsSemigroup_488 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_498 v0
  = case coe v0 of
      C_constructor_522 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemigroup._.isEquivalence
d_isEquivalence_502 ::
  T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_502 v0
  = coe d_isEquivalence_186 (coe d_isMagma_496 (coe v0))
-- Algebra.Structures.IsSemigroup._.isPartialEquivalence
d_isPartialEquivalence_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_504 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_504 v5
du_isPartialEquivalence_504 ::
  T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_504 v0
  = let v1 = d_isMagma_496 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_186 (coe v1)))
-- Algebra.Structures.IsSemigroup._.refl
d_refl_506 :: T_IsSemigroup_488 -> AgdaAny -> AgdaAny
d_refl_506 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe d_isMagma_496 (coe v0)))
-- Algebra.Structures.IsSemigroup._.reflexive
d_reflexive_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemigroup_488 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_508 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_508 v5
du_reflexive_508 ::
  T_IsSemigroup_488 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_508 v0
  = let v1 = d_isMagma_496 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_186 (coe v1)) v2)
-- Algebra.Structures.IsSemigroup._.setoid
d_setoid_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_510 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_510 v5
du_setoid_510 ::
  T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_510 v0 = coe du_setoid_202 (coe d_isMagma_496 (coe v0))
-- Algebra.Structures.IsSemigroup._.sym
d_sym_512 ::
  T_IsSemigroup_488 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_512 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe d_isMagma_496 (coe v0)))
-- Algebra.Structures.IsSemigroup._.trans
d_trans_514 ::
  T_IsSemigroup_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_514 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe d_isMagma_496 (coe v0)))
-- Algebra.Structures.IsSemigroup._.∙-cong
d_'8729''45'cong_516 ::
  T_IsSemigroup_488 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_516 v0
  = coe d_'8729''45'cong_188 (coe d_isMagma_496 (coe v0))
-- Algebra.Structures.IsSemigroup._.∙-congʳ
d_'8729''45'cong'691'_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemigroup_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_518 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_518 v5
du_'8729''45'cong'691'_518 ::
  T_IsSemigroup_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_518 v0
  = let v1 = d_isMagma_496 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsSemigroup._.∙-congˡ
d_'8729''45'cong'737'_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemigroup_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_520 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_520 v5
du_'8729''45'cong'737'_520 ::
  T_IsSemigroup_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_520 v0
  = let v1 = d_isMagma_496 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsBand
d_IsBand_526 a0 a1 a2 a3 a4 = ()
data T_IsBand_526
  = C_constructor_564 T_IsSemigroup_488 (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsBand.isSemigroup
d_isSemigroup_534 :: T_IsBand_526 -> T_IsSemigroup_488
d_isSemigroup_534 v0
  = case coe v0 of
      C_constructor_564 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsBand.idem
d_idem_536 :: T_IsBand_526 -> AgdaAny -> AgdaAny
d_idem_536 v0
  = case coe v0 of
      C_constructor_564 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsBand._.assoc
d_assoc_540 ::
  T_IsBand_526 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_540 v0 = coe d_assoc_498 (coe d_isSemigroup_534 (coe v0))
-- Algebra.Structures.IsBand._.isEquivalence
d_isEquivalence_542 ::
  T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_542 v0
  = coe
      d_isEquivalence_186
      (coe d_isMagma_496 (coe d_isSemigroup_534 (coe v0)))
-- Algebra.Structures.IsBand._.isMagma
d_isMagma_544 :: T_IsBand_526 -> T_IsMagma_178
d_isMagma_544 v0
  = coe d_isMagma_496 (coe d_isSemigroup_534 (coe v0))
-- Algebra.Structures.IsBand._.isPartialEquivalence
d_isPartialEquivalence_546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_546 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_546 v5
du_isPartialEquivalence_546 ::
  T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_546 v0
  = let v1 = d_isSemigroup_534 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe d_isEquivalence_186 (coe v2))))
-- Algebra.Structures.IsBand._.refl
d_refl_548 :: T_IsBand_526 -> AgdaAny -> AgdaAny
d_refl_548 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe d_isMagma_496 (coe d_isSemigroup_534 (coe v0))))
-- Algebra.Structures.IsBand._.reflexive
d_reflexive_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsBand_526 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_550 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_550 v5
du_reflexive_550 ::
  T_IsBand_526 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_550 v0
  = let v1 = d_isSemigroup_534 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe d_isEquivalence_186 (coe v2)) v3))
-- Algebra.Structures.IsBand._.setoid
d_setoid_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsBand_526 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_552 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_552 v5
du_setoid_552 ::
  T_IsBand_526 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_552 v0
  = let v1 = d_isSemigroup_534 (coe v0) in
    coe (coe du_setoid_202 (coe d_isMagma_496 (coe v1)))
-- Algebra.Structures.IsBand._.sym
d_sym_554 ::
  T_IsBand_526 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_554 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe d_isMagma_496 (coe d_isSemigroup_534 (coe v0))))
-- Algebra.Structures.IsBand._.trans
d_trans_556 ::
  T_IsBand_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_556 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe d_isMagma_496 (coe d_isSemigroup_534 (coe v0))))
-- Algebra.Structures.IsBand._.∙-cong
d_'8729''45'cong_558 ::
  T_IsBand_526 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_558 v0
  = coe
      d_'8729''45'cong_188
      (coe d_isMagma_496 (coe d_isSemigroup_534 (coe v0)))
-- Algebra.Structures.IsBand._.∙-congʳ
d_'8729''45'cong'691'_560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsBand_526 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_560 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_560 v5
du_'8729''45'cong'691'_560 ::
  T_IsBand_526 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_560 v0
  = let v1 = d_isSemigroup_534 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsBand._.∙-congˡ
d_'8729''45'cong'737'_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsBand_526 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_562 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_562 v5
du_'8729''45'cong'737'_562 ::
  T_IsBand_526 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_562 v0
  = let v1 = d_isSemigroup_534 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsCommutativeSemigroup
d_IsCommutativeSemigroup_568 a0 a1 a2 a3 a4 = ()
data T_IsCommutativeSemigroup_568
  = C_constructor_608 T_IsSemigroup_488
                      (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_576 ::
  T_IsCommutativeSemigroup_568 -> T_IsSemigroup_488
d_isSemigroup_576 v0
  = case coe v0 of
      C_constructor_608 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemigroup.comm
d_comm_578 ::
  T_IsCommutativeSemigroup_568 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_578 v0
  = case coe v0 of
      C_constructor_608 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemigroup._.assoc
d_assoc_582 ::
  T_IsCommutativeSemigroup_568 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_582 v0 = coe d_assoc_498 (coe d_isSemigroup_576 (coe v0))
-- Algebra.Structures.IsCommutativeSemigroup._.isEquivalence
d_isEquivalence_584 ::
  T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_584 v0
  = coe
      d_isEquivalence_186
      (coe d_isMagma_496 (coe d_isSemigroup_576 (coe v0)))
-- Algebra.Structures.IsCommutativeSemigroup._.isMagma
d_isMagma_586 :: T_IsCommutativeSemigroup_568 -> T_IsMagma_178
d_isMagma_586 v0
  = coe d_isMagma_496 (coe d_isSemigroup_576 (coe v0))
-- Algebra.Structures.IsCommutativeSemigroup._.isPartialEquivalence
d_isPartialEquivalence_588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_588 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_588 v5
du_isPartialEquivalence_588 ::
  T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_588 v0
  = let v1 = d_isSemigroup_576 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe d_isEquivalence_186 (coe v2))))
-- Algebra.Structures.IsCommutativeSemigroup._.refl
d_refl_590 :: T_IsCommutativeSemigroup_568 -> AgdaAny -> AgdaAny
d_refl_590 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe d_isMagma_496 (coe d_isSemigroup_576 (coe v0))))
-- Algebra.Structures.IsCommutativeSemigroup._.reflexive
d_reflexive_592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_568 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_592 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_592 v5
du_reflexive_592 ::
  T_IsCommutativeSemigroup_568 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_592 v0
  = let v1 = d_isSemigroup_576 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe d_isEquivalence_186 (coe v2)) v3))
-- Algebra.Structures.IsCommutativeSemigroup._.setoid
d_setoid_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_594 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_594 v5
du_setoid_594 ::
  T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_594 v0
  = let v1 = d_isSemigroup_576 (coe v0) in
    coe (coe du_setoid_202 (coe d_isMagma_496 (coe v1)))
-- Algebra.Structures.IsCommutativeSemigroup._.sym
d_sym_596 ::
  T_IsCommutativeSemigroup_568 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_596 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe d_isMagma_496 (coe d_isSemigroup_576 (coe v0))))
-- Algebra.Structures.IsCommutativeSemigroup._.trans
d_trans_598 ::
  T_IsCommutativeSemigroup_568 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_598 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe d_isMagma_496 (coe d_isSemigroup_576 (coe v0))))
-- Algebra.Structures.IsCommutativeSemigroup._.∙-cong
d_'8729''45'cong_600 ::
  T_IsCommutativeSemigroup_568 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_600 v0
  = coe
      d_'8729''45'cong_188
      (coe d_isMagma_496 (coe d_isSemigroup_576 (coe v0)))
-- Algebra.Structures.IsCommutativeSemigroup._.∙-congʳ
d_'8729''45'cong'691'_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_568 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_602 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_602 v5
du_'8729''45'cong'691'_602 ::
  T_IsCommutativeSemigroup_568 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_602 v0
  = let v1 = d_isSemigroup_576 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsCommutativeSemigroup._.∙-congˡ
d_'8729''45'cong'737'_604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_568 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_604 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_604 v5
du_'8729''45'cong'737'_604 ::
  T_IsCommutativeSemigroup_568 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_604 v0
  = let v1 = d_isSemigroup_576 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsCommutativeSemigroup.isCommutativeMagma
d_isCommutativeMagma_606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_568 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_606 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_606 v5
du_isCommutativeMagma_606 ::
  T_IsCommutativeSemigroup_568 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_606 v0
  = coe
      C_constructor_248
      (coe d_isMagma_496 (coe d_isSemigroup_576 (coe v0)))
      (coe d_comm_578 (coe v0))
-- Algebra.Structures.IsCommutativeBand
d_IsCommutativeBand_612 a0 a1 a2 a3 a4 = ()
data T_IsCommutativeBand_612
  = C_constructor_660 T_IsBand_526 (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeBand.isBand
d_isBand_620 :: T_IsCommutativeBand_612 -> T_IsBand_526
d_isBand_620 v0
  = case coe v0 of
      C_constructor_660 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeBand.comm
d_comm_622 ::
  T_IsCommutativeBand_612 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_622 v0
  = case coe v0 of
      C_constructor_660 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeBand._.assoc
d_assoc_626 ::
  T_IsCommutativeBand_612 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_626 v0
  = coe
      d_assoc_498 (coe d_isSemigroup_534 (coe d_isBand_620 (coe v0)))
-- Algebra.Structures.IsCommutativeBand._.idem
d_idem_628 :: T_IsCommutativeBand_612 -> AgdaAny -> AgdaAny
d_idem_628 v0 = coe d_idem_536 (coe d_isBand_620 (coe v0))
-- Algebra.Structures.IsCommutativeBand._.isEquivalence
d_isEquivalence_630 ::
  T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_630 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496 (coe d_isSemigroup_534 (coe d_isBand_620 (coe v0))))
-- Algebra.Structures.IsCommutativeBand._.isMagma
d_isMagma_632 :: T_IsCommutativeBand_612 -> T_IsMagma_178
d_isMagma_632 v0
  = coe
      d_isMagma_496 (coe d_isSemigroup_534 (coe d_isBand_620 (coe v0)))
-- Algebra.Structures.IsCommutativeBand._.isPartialEquivalence
d_isPartialEquivalence_634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_634 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_634 v5
du_isPartialEquivalence_634 ::
  T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_634 v0
  = let v1 = d_isBand_620 (coe v0) in
    coe
      (let v2 = d_isSemigroup_534 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.IsCommutativeBand._.isSemigroup
d_isSemigroup_636 :: T_IsCommutativeBand_612 -> T_IsSemigroup_488
d_isSemigroup_636 v0
  = coe d_isSemigroup_534 (coe d_isBand_620 (coe v0))
-- Algebra.Structures.IsCommutativeBand._.refl
d_refl_638 :: T_IsCommutativeBand_612 -> AgdaAny -> AgdaAny
d_refl_638 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496 (coe d_isSemigroup_534 (coe d_isBand_620 (coe v0)))))
-- Algebra.Structures.IsCommutativeBand._.reflexive
d_reflexive_640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_640 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_640 v5
du_reflexive_640 ::
  T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_640 v0
  = let v1 = d_isBand_620 (coe v0) in
    coe
      (let v2 = d_isSemigroup_534 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_186 (coe v3)) v4)))
-- Algebra.Structures.IsCommutativeBand._.setoid
d_setoid_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_642 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_642 v5
du_setoid_642 ::
  T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_642 v0
  = let v1 = d_isBand_620 (coe v0) in
    coe
      (let v2 = d_isSemigroup_534 (coe v1) in
       coe (coe du_setoid_202 (coe d_isMagma_496 (coe v2))))
-- Algebra.Structures.IsCommutativeBand._.sym
d_sym_644 ::
  T_IsCommutativeBand_612 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_644 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496 (coe d_isSemigroup_534 (coe d_isBand_620 (coe v0)))))
-- Algebra.Structures.IsCommutativeBand._.trans
d_trans_646 ::
  T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_646 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496 (coe d_isSemigroup_534 (coe d_isBand_620 (coe v0)))))
-- Algebra.Structures.IsCommutativeBand._.∙-cong
d_'8729''45'cong_648 ::
  T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_648 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496 (coe d_isSemigroup_534 (coe d_isBand_620 (coe v0))))
-- Algebra.Structures.IsCommutativeBand._.∙-congʳ
d_'8729''45'cong'691'_650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_650 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_650 v5
du_'8729''45'cong'691'_650 ::
  T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_650 v0
  = let v1 = d_isBand_620 (coe v0) in
    coe
      (let v2 = d_isSemigroup_534 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsCommutativeBand._.∙-congˡ
d_'8729''45'cong'737'_652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_652 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_652 v5
du_'8729''45'cong'737'_652 ::
  T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_652 v0
  = let v1 = d_isBand_620 (coe v0) in
    coe
      (let v2 = d_isSemigroup_534 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsCommutativeBand.isCommutativeSemigroup
d_isCommutativeSemigroup_654 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_612 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_654 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_654 v5
du_isCommutativeSemigroup_654 ::
  T_IsCommutativeBand_612 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_654 v0
  = coe
      C_constructor_608
      (coe d_isSemigroup_534 (coe d_isBand_620 (coe v0)))
      (coe d_comm_622 (coe v0))
-- Algebra.Structures.IsCommutativeBand._.isCommutativeMagma
d_isCommutativeMagma_658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_612 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_658 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_658 v5
du_isCommutativeMagma_658 ::
  T_IsCommutativeBand_612 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_658 v0
  = coe
      du_isCommutativeMagma_606
      (coe du_isCommutativeSemigroup_654 (coe v0))
-- Algebra.Structures.IsUnitalMagma
d_IsUnitalMagma_666 a0 a1 a2 a3 a4 a5 = ()
data T_IsUnitalMagma_666
  = C_constructor_706 T_IsMagma_178
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsUnitalMagma.isMagma
d_isMagma_676 :: T_IsUnitalMagma_666 -> T_IsMagma_178
d_isMagma_676 v0
  = case coe v0 of
      C_constructor_706 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsUnitalMagma.identity
d_identity_678 ::
  T_IsUnitalMagma_666 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_678 v0
  = case coe v0 of
      C_constructor_706 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsUnitalMagma._.isEquivalence
d_isEquivalence_682 ::
  T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_682 v0
  = coe d_isEquivalence_186 (coe d_isMagma_676 (coe v0))
-- Algebra.Structures.IsUnitalMagma._.isPartialEquivalence
d_isPartialEquivalence_684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_684 v6
du_isPartialEquivalence_684 ::
  T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_684 v0
  = let v1 = d_isMagma_676 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_186 (coe v1)))
-- Algebra.Structures.IsUnitalMagma._.refl
d_refl_686 :: T_IsUnitalMagma_666 -> AgdaAny -> AgdaAny
d_refl_686 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe d_isMagma_676 (coe v0)))
-- Algebra.Structures.IsUnitalMagma._.reflexive
d_reflexive_688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsUnitalMagma_666 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_688 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_688 v6
du_reflexive_688 ::
  T_IsUnitalMagma_666 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_688 v0
  = let v1 = d_isMagma_676 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_186 (coe v1)) v2)
-- Algebra.Structures.IsUnitalMagma._.setoid
d_setoid_690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_690 v6
du_setoid_690 ::
  T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_690 v0 = coe du_setoid_202 (coe d_isMagma_676 (coe v0))
-- Algebra.Structures.IsUnitalMagma._.sym
d_sym_692 ::
  T_IsUnitalMagma_666 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_692 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe d_isMagma_676 (coe v0)))
-- Algebra.Structures.IsUnitalMagma._.trans
d_trans_694 ::
  T_IsUnitalMagma_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_694 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe d_isMagma_676 (coe v0)))
-- Algebra.Structures.IsUnitalMagma._.∙-cong
d_'8729''45'cong_696 ::
  T_IsUnitalMagma_666 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_696 v0
  = coe d_'8729''45'cong_188 (coe d_isMagma_676 (coe v0))
-- Algebra.Structures.IsUnitalMagma._.∙-congʳ
d_'8729''45'cong'691'_698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsUnitalMagma_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_698 v6
du_'8729''45'cong'691'_698 ::
  T_IsUnitalMagma_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_698 v0
  = let v1 = d_isMagma_676 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsUnitalMagma._.∙-congˡ
d_'8729''45'cong'737'_700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsUnitalMagma_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_700 v6
du_'8729''45'cong'737'_700 ::
  T_IsUnitalMagma_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_700 v0
  = let v1 = d_isMagma_676 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsUnitalMagma.identityˡ
d_identity'737'_702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsUnitalMagma_666 -> AgdaAny -> AgdaAny
d_identity'737'_702 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_702 v6
du_identity'737'_702 :: T_IsUnitalMagma_666 -> AgdaAny -> AgdaAny
du_identity'737'_702 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_identity_678 (coe v0))
-- Algebra.Structures.IsUnitalMagma.identityʳ
d_identity'691'_704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsUnitalMagma_666 -> AgdaAny -> AgdaAny
d_identity'691'_704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_704 v6
du_identity'691'_704 :: T_IsUnitalMagma_666 -> AgdaAny -> AgdaAny
du_identity'691'_704 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_identity_678 (coe v0))
-- Algebra.Structures.IsMonoid
d_IsMonoid_712 a0 a1 a2 a3 a4 a5 = ()
data T_IsMonoid_712
  = C_constructor_758 T_IsSemigroup_488
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsMonoid.isSemigroup
d_isSemigroup_722 :: T_IsMonoid_712 -> T_IsSemigroup_488
d_isSemigroup_722 v0
  = case coe v0 of
      C_constructor_758 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMonoid.identity
d_identity_724 ::
  T_IsMonoid_712 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_724 v0
  = case coe v0 of
      C_constructor_758 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMonoid._.assoc
d_assoc_728 ::
  T_IsMonoid_712 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_728 v0 = coe d_assoc_498 (coe d_isSemigroup_722 (coe v0))
-- Algebra.Structures.IsMonoid._.isEquivalence
d_isEquivalence_730 ::
  T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_730 v0
  = coe
      d_isEquivalence_186
      (coe d_isMagma_496 (coe d_isSemigroup_722 (coe v0)))
-- Algebra.Structures.IsMonoid._.isMagma
d_isMagma_732 :: T_IsMonoid_712 -> T_IsMagma_178
d_isMagma_732 v0
  = coe d_isMagma_496 (coe d_isSemigroup_722 (coe v0))
-- Algebra.Structures.IsMonoid._.isPartialEquivalence
d_isPartialEquivalence_734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_734 v6
du_isPartialEquivalence_734 ::
  T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_734 v0
  = let v1 = d_isSemigroup_722 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe d_isEquivalence_186 (coe v2))))
-- Algebra.Structures.IsMonoid._.refl
d_refl_736 :: T_IsMonoid_712 -> AgdaAny -> AgdaAny
d_refl_736 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe d_isMagma_496 (coe d_isSemigroup_722 (coe v0))))
-- Algebra.Structures.IsMonoid._.reflexive
d_reflexive_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMonoid_712 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_738 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_738 v6
du_reflexive_738 ::
  T_IsMonoid_712 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_738 v0
  = let v1 = d_isSemigroup_722 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe d_isEquivalence_186 (coe v2)) v3))
-- Algebra.Structures.IsMonoid._.setoid
d_setoid_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMonoid_712 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_740 v6
du_setoid_740 ::
  T_IsMonoid_712 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_740 v0
  = let v1 = d_isSemigroup_722 (coe v0) in
    coe (coe du_setoid_202 (coe d_isMagma_496 (coe v1)))
-- Algebra.Structures.IsMonoid._.sym
d_sym_742 ::
  T_IsMonoid_712 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_742 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe d_isMagma_496 (coe d_isSemigroup_722 (coe v0))))
-- Algebra.Structures.IsMonoid._.trans
d_trans_744 ::
  T_IsMonoid_712 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_744 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe d_isMagma_496 (coe d_isSemigroup_722 (coe v0))))
-- Algebra.Structures.IsMonoid._.∙-cong
d_'8729''45'cong_746 ::
  T_IsMonoid_712 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_746 v0
  = coe
      d_'8729''45'cong_188
      (coe d_isMagma_496 (coe d_isSemigroup_722 (coe v0)))
-- Algebra.Structures.IsMonoid._.∙-congʳ
d_'8729''45'cong'691'_748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMonoid_712 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_748 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_748 v6
du_'8729''45'cong'691'_748 ::
  T_IsMonoid_712 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_748 v0
  = let v1 = d_isSemigroup_722 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsMonoid._.∙-congˡ
d_'8729''45'cong'737'_750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMonoid_712 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_750 v6
du_'8729''45'cong'737'_750 ::
  T_IsMonoid_712 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_750 v0
  = let v1 = d_isSemigroup_722 (coe v0) in
    coe
      (let v2 = d_isMagma_496 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsMonoid.identityˡ
d_identity'737'_752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMonoid_712 -> AgdaAny -> AgdaAny
d_identity'737'_752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_752 v6
du_identity'737'_752 :: T_IsMonoid_712 -> AgdaAny -> AgdaAny
du_identity'737'_752 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_identity_724 (coe v0))
-- Algebra.Structures.IsMonoid.identityʳ
d_identity'691'_754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMonoid_712 -> AgdaAny -> AgdaAny
d_identity'691'_754 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_754 v6
du_identity'691'_754 :: T_IsMonoid_712 -> AgdaAny -> AgdaAny
du_identity'691'_754 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_identity_724 (coe v0))
-- Algebra.Structures.IsMonoid.isUnitalMagma
d_isUnitalMagma_756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMonoid_712 -> T_IsUnitalMagma_666
d_isUnitalMagma_756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isUnitalMagma_756 v6
du_isUnitalMagma_756 :: T_IsMonoid_712 -> T_IsUnitalMagma_666
du_isUnitalMagma_756 v0
  = coe
      C_constructor_706
      (coe d_isMagma_496 (coe d_isSemigroup_722 (coe v0)))
      (coe d_identity_724 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid
d_IsCommutativeMonoid_764 a0 a1 a2 a3 a4 a5 = ()
data T_IsCommutativeMonoid_764
  = C_constructor_820 T_IsMonoid_712 (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeMonoid.isMonoid
d_isMonoid_774 :: T_IsCommutativeMonoid_764 -> T_IsMonoid_712
d_isMonoid_774 v0
  = case coe v0 of
      C_constructor_820 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeMonoid.comm
d_comm_776 ::
  T_IsCommutativeMonoid_764 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_776 v0
  = case coe v0 of
      C_constructor_820 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeMonoid._.assoc
d_assoc_780 ::
  T_IsCommutativeMonoid_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_780 v0
  = coe
      d_assoc_498 (coe d_isSemigroup_722 (coe d_isMonoid_774 (coe v0)))
-- Algebra.Structures.IsCommutativeMonoid._.identity
d_identity_782 ::
  T_IsCommutativeMonoid_764 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_782 v0
  = coe d_identity_724 (coe d_isMonoid_774 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.identityʳ
d_identity'691'_784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeMonoid_764 -> AgdaAny -> AgdaAny
d_identity'691'_784 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_784 v6
du_identity'691'_784 ::
  T_IsCommutativeMonoid_764 -> AgdaAny -> AgdaAny
du_identity'691'_784 v0
  = coe du_identity'691'_754 (coe d_isMonoid_774 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.identityˡ
d_identity'737'_786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeMonoid_764 -> AgdaAny -> AgdaAny
d_identity'737'_786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_786 v6
du_identity'737'_786 ::
  T_IsCommutativeMonoid_764 -> AgdaAny -> AgdaAny
du_identity'737'_786 v0
  = coe du_identity'737'_752 (coe d_isMonoid_774 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.isEquivalence
d_isEquivalence_788 ::
  T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_788 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe d_isSemigroup_722 (coe d_isMonoid_774 (coe v0))))
-- Algebra.Structures.IsCommutativeMonoid._.isMagma
d_isMagma_790 :: T_IsCommutativeMonoid_764 -> T_IsMagma_178
d_isMagma_790 v0
  = coe
      d_isMagma_496 (coe d_isSemigroup_722 (coe d_isMonoid_774 (coe v0)))
-- Algebra.Structures.IsCommutativeMonoid._.isPartialEquivalence
d_isPartialEquivalence_792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_792 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_792 v6
du_isPartialEquivalence_792 ::
  T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_792 v0
  = let v1 = d_isMonoid_774 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.IsCommutativeMonoid._.isSemigroup
d_isSemigroup_794 :: T_IsCommutativeMonoid_764 -> T_IsSemigroup_488
d_isSemigroup_794 v0
  = coe d_isSemigroup_722 (coe d_isMonoid_774 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.isUnitalMagma
d_isUnitalMagma_796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeMonoid_764 -> T_IsUnitalMagma_666
d_isUnitalMagma_796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isUnitalMagma_796 v6
du_isUnitalMagma_796 ::
  T_IsCommutativeMonoid_764 -> T_IsUnitalMagma_666
du_isUnitalMagma_796 v0
  = coe du_isUnitalMagma_756 (coe d_isMonoid_774 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.refl
d_refl_798 :: T_IsCommutativeMonoid_764 -> AgdaAny -> AgdaAny
d_refl_798 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_774 (coe v0)))))
-- Algebra.Structures.IsCommutativeMonoid._.reflexive
d_reflexive_800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_764 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_800 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_800 v6
du_reflexive_800 ::
  T_IsCommutativeMonoid_764 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_800 v0
  = let v1 = d_isMonoid_774 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_186 (coe v3)) v4)))
-- Algebra.Structures.IsCommutativeMonoid._.setoid
d_setoid_802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_802 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_802 v6
du_setoid_802 ::
  T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_802 v0
  = let v1 = d_isMonoid_774 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe (coe du_setoid_202 (coe d_isMagma_496 (coe v2))))
-- Algebra.Structures.IsCommutativeMonoid._.sym
d_sym_804 ::
  T_IsCommutativeMonoid_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_804 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_774 (coe v0)))))
-- Algebra.Structures.IsCommutativeMonoid._.trans
d_trans_806 ::
  T_IsCommutativeMonoid_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_806 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_774 (coe v0)))))
-- Algebra.Structures.IsCommutativeMonoid._.∙-cong
d_'8729''45'cong_808 ::
  T_IsCommutativeMonoid_764 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_808 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe d_isSemigroup_722 (coe d_isMonoid_774 (coe v0))))
-- Algebra.Structures.IsCommutativeMonoid._.∙-congʳ
d_'8729''45'cong'691'_810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_810 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_810 v6
du_'8729''45'cong'691'_810 ::
  T_IsCommutativeMonoid_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_810 v0
  = let v1 = d_isMonoid_774 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsCommutativeMonoid._.∙-congˡ
d_'8729''45'cong'737'_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_812 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_812 v6
du_'8729''45'cong'737'_812 ::
  T_IsCommutativeMonoid_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_812 v0
  = let v1 = d_isMonoid_774 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsCommutativeMonoid.isCommutativeSemigroup
d_isCommutativeSemigroup_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_764 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_814 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeSemigroup_814 v6
du_isCommutativeSemigroup_814 ::
  T_IsCommutativeMonoid_764 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_814 v0
  = coe
      C_constructor_608
      (coe d_isSemigroup_722 (coe d_isMonoid_774 (coe v0)))
      (coe d_comm_776 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.isCommutativeMagma
d_isCommutativeMagma_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeMonoid_764 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_818 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeMagma_818 v6
du_isCommutativeMagma_818 ::
  T_IsCommutativeMonoid_764 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_818 v0
  = coe
      du_isCommutativeMagma_606
      (coe du_isCommutativeSemigroup_814 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid
d_IsIdempotentMonoid_826 a0 a1 a2 a3 a4 a5 = ()
data T_IsIdempotentMonoid_826
  = C_constructor_878 T_IsMonoid_712 (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsIdempotentMonoid.isMonoid
d_isMonoid_836 :: T_IsIdempotentMonoid_826 -> T_IsMonoid_712
d_isMonoid_836 v0
  = case coe v0 of
      C_constructor_878 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentMonoid.idem
d_idem_838 :: T_IsIdempotentMonoid_826 -> AgdaAny -> AgdaAny
d_idem_838 v0
  = case coe v0 of
      C_constructor_878 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentMonoid._.assoc
d_assoc_842 ::
  T_IsIdempotentMonoid_826 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_842 v0
  = coe
      d_assoc_498 (coe d_isSemigroup_722 (coe d_isMonoid_836 (coe v0)))
-- Algebra.Structures.IsIdempotentMonoid._.identity
d_identity_844 ::
  T_IsIdempotentMonoid_826 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_844 v0
  = coe d_identity_724 (coe d_isMonoid_836 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid._.identityʳ
d_identity'691'_846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsIdempotentMonoid_826 -> AgdaAny -> AgdaAny
d_identity'691'_846 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_846 v6
du_identity'691'_846 ::
  T_IsIdempotentMonoid_826 -> AgdaAny -> AgdaAny
du_identity'691'_846 v0
  = coe du_identity'691'_754 (coe d_isMonoid_836 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid._.identityˡ
d_identity'737'_848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsIdempotentMonoid_826 -> AgdaAny -> AgdaAny
d_identity'737'_848 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_848 v6
du_identity'737'_848 ::
  T_IsIdempotentMonoid_826 -> AgdaAny -> AgdaAny
du_identity'737'_848 v0
  = coe du_identity'737'_752 (coe d_isMonoid_836 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid._.isEquivalence
d_isEquivalence_850 ::
  T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_850 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe d_isSemigroup_722 (coe d_isMonoid_836 (coe v0))))
-- Algebra.Structures.IsIdempotentMonoid._.isMagma
d_isMagma_852 :: T_IsIdempotentMonoid_826 -> T_IsMagma_178
d_isMagma_852 v0
  = coe
      d_isMagma_496 (coe d_isSemigroup_722 (coe d_isMonoid_836 (coe v0)))
-- Algebra.Structures.IsIdempotentMonoid._.isPartialEquivalence
d_isPartialEquivalence_854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_854 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_854 v6
du_isPartialEquivalence_854 ::
  T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_854 v0
  = let v1 = d_isMonoid_836 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.IsIdempotentMonoid._.isSemigroup
d_isSemigroup_856 :: T_IsIdempotentMonoid_826 -> T_IsSemigroup_488
d_isSemigroup_856 v0
  = coe d_isSemigroup_722 (coe d_isMonoid_836 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid._.isUnitalMagma
d_isUnitalMagma_858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsIdempotentMonoid_826 -> T_IsUnitalMagma_666
d_isUnitalMagma_858 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isUnitalMagma_858 v6
du_isUnitalMagma_858 ::
  T_IsIdempotentMonoid_826 -> T_IsUnitalMagma_666
du_isUnitalMagma_858 v0
  = coe du_isUnitalMagma_756 (coe d_isMonoid_836 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid._.refl
d_refl_860 :: T_IsIdempotentMonoid_826 -> AgdaAny -> AgdaAny
d_refl_860 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_836 (coe v0)))))
-- Algebra.Structures.IsIdempotentMonoid._.reflexive
d_reflexive_862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentMonoid_826 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_862 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_862 v6
du_reflexive_862 ::
  T_IsIdempotentMonoid_826 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_862 v0
  = let v1 = d_isMonoid_836 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_186 (coe v3)) v4)))
-- Algebra.Structures.IsIdempotentMonoid._.setoid
d_setoid_864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_864 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_864 v6
du_setoid_864 ::
  T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_864 v0
  = let v1 = d_isMonoid_836 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe (coe du_setoid_202 (coe d_isMagma_496 (coe v2))))
-- Algebra.Structures.IsIdempotentMonoid._.sym
d_sym_866 ::
  T_IsIdempotentMonoid_826 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_866 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_836 (coe v0)))))
-- Algebra.Structures.IsIdempotentMonoid._.trans
d_trans_868 ::
  T_IsIdempotentMonoid_826 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_868 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_836 (coe v0)))))
-- Algebra.Structures.IsIdempotentMonoid._.∙-cong
d_'8729''45'cong_870 ::
  T_IsIdempotentMonoid_826 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_870 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe d_isSemigroup_722 (coe d_isMonoid_836 (coe v0))))
-- Algebra.Structures.IsIdempotentMonoid._.∙-congʳ
d_'8729''45'cong'691'_872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentMonoid_826 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_872 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_872 v6
du_'8729''45'cong'691'_872 ::
  T_IsIdempotentMonoid_826 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_872 v0
  = let v1 = d_isMonoid_836 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsIdempotentMonoid._.∙-congˡ
d_'8729''45'cong'737'_874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentMonoid_826 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_874 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_874 v6
du_'8729''45'cong'737'_874 ::
  T_IsIdempotentMonoid_826 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_874 v0
  = let v1 = d_isMonoid_836 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsIdempotentMonoid.isBand
d_isBand_876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsIdempotentMonoid_826 -> T_IsBand_526
d_isBand_876 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isBand_876 v6
du_isBand_876 :: T_IsIdempotentMonoid_826 -> T_IsBand_526
du_isBand_876 v0
  = coe
      C_constructor_564
      (coe d_isSemigroup_722 (coe d_isMonoid_836 (coe v0)))
      (coe d_idem_838 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid
d_IsIdempotentCommutativeMonoid_884 a0 a1 a2 a3 a4 a5 = ()
data T_IsIdempotentCommutativeMonoid_884
  = C_constructor_950 T_IsCommutativeMonoid_764 (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsIdempotentCommutativeMonoid.isCommutativeMonoid
d_isCommutativeMonoid_894 ::
  T_IsIdempotentCommutativeMonoid_884 -> T_IsCommutativeMonoid_764
d_isCommutativeMonoid_894 v0
  = case coe v0 of
      C_constructor_950 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentCommutativeMonoid.idem
d_idem_896 ::
  T_IsIdempotentCommutativeMonoid_884 -> AgdaAny -> AgdaAny
d_idem_896 v0
  = case coe v0 of
      C_constructor_950 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.assoc
d_assoc_900 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_900 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe d_isMonoid_774 (coe d_isCommutativeMonoid_894 (coe v0))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.comm
d_comm_902 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_902 v0
  = coe d_comm_776 (coe d_isCommutativeMonoid_894 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.identity
d_identity_904 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_904 v0
  = coe
      d_identity_724
      (coe d_isMonoid_774 (coe d_isCommutativeMonoid_894 (coe v0)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.identityʳ
d_identity'691'_906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 -> AgdaAny -> AgdaAny
d_identity'691'_906 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_906 v6
du_identity'691'_906 ::
  T_IsIdempotentCommutativeMonoid_884 -> AgdaAny -> AgdaAny
du_identity'691'_906 v0
  = let v1 = d_isCommutativeMonoid_894 (coe v0) in
    coe (coe du_identity'691'_754 (coe d_isMonoid_774 (coe v1)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.identityˡ
d_identity'737'_908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 -> AgdaAny -> AgdaAny
d_identity'737'_908 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_908 v6
du_identity'737'_908 ::
  T_IsIdempotentCommutativeMonoid_884 -> AgdaAny -> AgdaAny
du_identity'737'_908 v0
  = let v1 = d_isCommutativeMonoid_894 (coe v0) in
    coe (coe du_identity'737'_752 (coe d_isMonoid_774 (coe v1)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isCommutativeMagma
d_isCommutativeMagma_910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_910 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeMagma_910 v6
du_isCommutativeMagma_910 ::
  T_IsIdempotentCommutativeMonoid_884 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_910 v0
  = let v1 = d_isCommutativeMonoid_894 (coe v0) in
    coe
      (coe
         du_isCommutativeMagma_606
         (coe du_isCommutativeSemigroup_814 (coe v1)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isCommutativeSemigroup
d_isCommutativeSemigroup_912 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_912 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeSemigroup_912 v6
du_isCommutativeSemigroup_912 ::
  T_IsIdempotentCommutativeMonoid_884 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_912 v0
  = coe
      du_isCommutativeSemigroup_814
      (coe d_isCommutativeMonoid_894 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isEquivalence
d_isEquivalence_914 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_914 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe d_isMonoid_774 (coe d_isCommutativeMonoid_894 (coe v0)))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isMagma
d_isMagma_916 ::
  T_IsIdempotentCommutativeMonoid_884 -> T_IsMagma_178
d_isMagma_916 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe d_isMonoid_774 (coe d_isCommutativeMonoid_894 (coe v0))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isMonoid
d_isMonoid_918 ::
  T_IsIdempotentCommutativeMonoid_884 -> T_IsMonoid_712
d_isMonoid_918 v0
  = coe d_isMonoid_774 (coe d_isCommutativeMonoid_894 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isPartialEquivalence
d_isPartialEquivalence_920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_920 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_920 v6
du_isPartialEquivalence_920 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_920 v0
  = let v1 = d_isCommutativeMonoid_894 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe d_isEquivalence_186 (coe v4))))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isSemigroup
d_isSemigroup_922 ::
  T_IsIdempotentCommutativeMonoid_884 -> T_IsSemigroup_488
d_isSemigroup_922 v0
  = coe
      d_isSemigroup_722
      (coe d_isMonoid_774 (coe d_isCommutativeMonoid_894 (coe v0)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isUnitalMagma
d_isUnitalMagma_924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 -> T_IsUnitalMagma_666
d_isUnitalMagma_924 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isUnitalMagma_924 v6
du_isUnitalMagma_924 ::
  T_IsIdempotentCommutativeMonoid_884 -> T_IsUnitalMagma_666
du_isUnitalMagma_924 v0
  = let v1 = d_isCommutativeMonoid_894 (coe v0) in
    coe (coe du_isUnitalMagma_756 (coe d_isMonoid_774 (coe v1)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.refl
d_refl_926 ::
  T_IsIdempotentCommutativeMonoid_884 -> AgdaAny -> AgdaAny
d_refl_926 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe d_isMonoid_774 (coe d_isCommutativeMonoid_894 (coe v0))))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.reflexive
d_reflexive_928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_928 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_928 v6
du_reflexive_928 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_928 v0
  = let v1 = d_isCommutativeMonoid_894 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe d_isEquivalence_186 (coe v4)) v5))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.setoid
d_setoid_930 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_930 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_930 v6
du_setoid_930 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_930 v0
  = let v1 = d_isCommutativeMonoid_894 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe (coe du_setoid_202 (coe d_isMagma_496 (coe v3)))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.sym
d_sym_932 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_932 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe d_isMonoid_774 (coe d_isCommutativeMonoid_894 (coe v0))))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.trans
d_trans_934 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_934 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe d_isMonoid_774 (coe d_isCommutativeMonoid_894 (coe v0))))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.∙-cong
d_'8729''45'cong_936 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_936 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe d_isMonoid_774 (coe d_isCommutativeMonoid_894 (coe v0)))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.∙-congʳ
d_'8729''45'cong'691'_938 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_938 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_938 v6
du_'8729''45'cong'691'_938 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_938 v0
  = let v1 = d_isCommutativeMonoid_894 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.∙-congˡ
d_'8729''45'cong'737'_940 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_940 v6
du_'8729''45'cong'737'_940 ::
  T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_940 v0
  = let v1 = d_isCommutativeMonoid_894 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid.isIdempotentMonoid
d_isIdempotentMonoid_942 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 -> T_IsIdempotentMonoid_826
d_isIdempotentMonoid_942 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isIdempotentMonoid_942 v6
du_isIdempotentMonoid_942 ::
  T_IsIdempotentCommutativeMonoid_884 -> T_IsIdempotentMonoid_826
du_isIdempotentMonoid_942 v0
  = coe
      C_constructor_878
      (coe d_isMonoid_774 (coe d_isCommutativeMonoid_894 (coe v0)))
      (coe d_idem_896 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isBand
d_isBand_946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsIdempotentCommutativeMonoid_884 -> T_IsBand_526
d_isBand_946 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isBand_946 v6
du_isBand_946 ::
  T_IsIdempotentCommutativeMonoid_884 -> T_IsBand_526
du_isBand_946 v0
  = coe du_isBand_876 (coe du_isIdempotentMonoid_942 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid.isCommutativeBand
d_isCommutativeBand_948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_884 -> T_IsCommutativeBand_612
d_isCommutativeBand_948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeBand_948 v6
du_isCommutativeBand_948 ::
  T_IsIdempotentCommutativeMonoid_884 -> T_IsCommutativeBand_612
du_isCommutativeBand_948 v0
  = coe
      C_constructor_660
      (coe du_isBand_876 (coe du_isIdempotentMonoid_942 (coe v0)))
      (coe d_comm_776 (coe d_isCommutativeMonoid_894 (coe v0)))
-- Algebra.Structures.IsInvertibleMagma
d_IsInvertibleMagma_958 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsInvertibleMagma_958
  = C_constructor_1004 T_IsMagma_178
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsInvertibleMagma.isMagma
d_isMagma_972 :: T_IsInvertibleMagma_958 -> T_IsMagma_178
d_isMagma_972 v0
  = case coe v0 of
      C_constructor_1004 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsInvertibleMagma.inverse
d_inverse_974 ::
  T_IsInvertibleMagma_958 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_974 v0
  = case coe v0 of
      C_constructor_1004 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsInvertibleMagma.⁻¹-cong
d_'8315''185''45'cong_976 ::
  T_IsInvertibleMagma_958 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_976 v0
  = case coe v0 of
      C_constructor_1004 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsInvertibleMagma._.isEquivalence
d_isEquivalence_980 ::
  T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_980 v0
  = coe d_isEquivalence_186 (coe d_isMagma_972 (coe v0))
-- Algebra.Structures.IsInvertibleMagma._.isPartialEquivalence
d_isPartialEquivalence_982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_982 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_982 v7
du_isPartialEquivalence_982 ::
  T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_982 v0
  = let v1 = d_isMagma_972 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_186 (coe v1)))
-- Algebra.Structures.IsInvertibleMagma._.refl
d_refl_984 :: T_IsInvertibleMagma_958 -> AgdaAny -> AgdaAny
d_refl_984 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe d_isMagma_972 (coe v0)))
-- Algebra.Structures.IsInvertibleMagma._.reflexive
d_reflexive_986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_958 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_986 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_986 v7
du_reflexive_986 ::
  T_IsInvertibleMagma_958 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_986 v0
  = let v1 = d_isMagma_972 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_186 (coe v1)) v2)
-- Algebra.Structures.IsInvertibleMagma._.setoid
d_setoid_988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_988 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_988 v7
du_setoid_988 ::
  T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_988 v0 = coe du_setoid_202 (coe d_isMagma_972 (coe v0))
-- Algebra.Structures.IsInvertibleMagma._.sym
d_sym_990 ::
  T_IsInvertibleMagma_958 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_990 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe d_isMagma_972 (coe v0)))
-- Algebra.Structures.IsInvertibleMagma._.trans
d_trans_992 ::
  T_IsInvertibleMagma_958 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_992 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe d_isMagma_972 (coe v0)))
-- Algebra.Structures.IsInvertibleMagma._.∙-cong
d_'8729''45'cong_994 ::
  T_IsInvertibleMagma_958 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_994 v0
  = coe d_'8729''45'cong_188 (coe d_isMagma_972 (coe v0))
-- Algebra.Structures.IsInvertibleMagma._.∙-congʳ
d_'8729''45'cong'691'_996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_958 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_996 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_996 v7
du_'8729''45'cong'691'_996 ::
  T_IsInvertibleMagma_958 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_996 v0
  = let v1 = d_isMagma_972 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsInvertibleMagma._.∙-congˡ
d_'8729''45'cong'737'_998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_958 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_998 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_998 v7
du_'8729''45'cong'737'_998 ::
  T_IsInvertibleMagma_958 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_998 v0
  = let v1 = d_isMagma_972 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsInvertibleMagma.inverseˡ
d_inverse'737'_1000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_958 -> AgdaAny -> AgdaAny
d_inverse'737'_1000 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'737'_1000 v7
du_inverse'737'_1000 ::
  T_IsInvertibleMagma_958 -> AgdaAny -> AgdaAny
du_inverse'737'_1000 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_inverse_974 (coe v0))
-- Algebra.Structures.IsInvertibleMagma.inverseʳ
d_inverse'691'_1002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_958 -> AgdaAny -> AgdaAny
d_inverse'691'_1002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'691'_1002 v7
du_inverse'691'_1002 ::
  T_IsInvertibleMagma_958 -> AgdaAny -> AgdaAny
du_inverse'691'_1002 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_inverse_974 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma
d_IsInvertibleUnitalMagma_1012 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsInvertibleUnitalMagma_1012
  = C_constructor_1066 T_IsInvertibleMagma_958
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsInvertibleUnitalMagma.isInvertibleMagma
d_isInvertibleMagma_1024 ::
  T_IsInvertibleUnitalMagma_1012 -> T_IsInvertibleMagma_958
d_isInvertibleMagma_1024 v0
  = case coe v0 of
      C_constructor_1066 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsInvertibleUnitalMagma.identity
d_identity_1026 ::
  T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1026 v0
  = case coe v0 of
      C_constructor_1066 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsInvertibleUnitalMagma._.inverse
d_inverse_1030 ::
  T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1030 v0
  = coe d_inverse_974 (coe d_isInvertibleMagma_1024 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma._.inverseʳ
d_inverse'691'_1032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_1012 -> AgdaAny -> AgdaAny
d_inverse'691'_1032 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'691'_1032 v7
du_inverse'691'_1032 ::
  T_IsInvertibleUnitalMagma_1012 -> AgdaAny -> AgdaAny
du_inverse'691'_1032 v0
  = coe du_inverse'691'_1002 (coe d_isInvertibleMagma_1024 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma._.inverseˡ
d_inverse'737'_1034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_1012 -> AgdaAny -> AgdaAny
d_inverse'737'_1034 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'737'_1034 v7
du_inverse'737'_1034 ::
  T_IsInvertibleUnitalMagma_1012 -> AgdaAny -> AgdaAny
du_inverse'737'_1034 v0
  = coe du_inverse'737'_1000 (coe d_isInvertibleMagma_1024 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma._.isEquivalence
d_isEquivalence_1036 ::
  T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1036 v0
  = coe
      d_isEquivalence_186
      (coe d_isMagma_972 (coe d_isInvertibleMagma_1024 (coe v0)))
-- Algebra.Structures.IsInvertibleUnitalMagma._.isMagma
d_isMagma_1038 :: T_IsInvertibleUnitalMagma_1012 -> T_IsMagma_178
d_isMagma_1038 v0
  = coe d_isMagma_972 (coe d_isInvertibleMagma_1024 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma._.isPartialEquivalence
d_isPartialEquivalence_1040 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1040 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1040 v7
du_isPartialEquivalence_1040 ::
  T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1040 v0
  = let v1 = d_isInvertibleMagma_1024 (coe v0) in
    coe
      (let v2 = d_isMagma_972 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe d_isEquivalence_186 (coe v2))))
-- Algebra.Structures.IsInvertibleUnitalMagma._.refl
d_refl_1042 :: T_IsInvertibleUnitalMagma_1012 -> AgdaAny -> AgdaAny
d_refl_1042 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe d_isMagma_972 (coe d_isInvertibleMagma_1024 (coe v0))))
-- Algebra.Structures.IsInvertibleUnitalMagma._.reflexive
d_reflexive_1044 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_1012 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1044 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1044 v7
du_reflexive_1044 ::
  T_IsInvertibleUnitalMagma_1012 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1044 v0
  = let v1 = d_isInvertibleMagma_1024 (coe v0) in
    coe
      (let v2 = d_isMagma_972 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe d_isEquivalence_186 (coe v2)) v3))
-- Algebra.Structures.IsInvertibleUnitalMagma._.setoid
d_setoid_1046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1046 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1046 v7
du_setoid_1046 ::
  T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1046 v0
  = let v1 = d_isInvertibleMagma_1024 (coe v0) in
    coe (coe du_setoid_202 (coe d_isMagma_972 (coe v1)))
-- Algebra.Structures.IsInvertibleUnitalMagma._.sym
d_sym_1048 ::
  T_IsInvertibleUnitalMagma_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1048 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe d_isMagma_972 (coe d_isInvertibleMagma_1024 (coe v0))))
-- Algebra.Structures.IsInvertibleUnitalMagma._.trans
d_trans_1050 ::
  T_IsInvertibleUnitalMagma_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1050 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe d_isMagma_972 (coe d_isInvertibleMagma_1024 (coe v0))))
-- Algebra.Structures.IsInvertibleUnitalMagma._.⁻¹-cong
d_'8315''185''45'cong_1052 ::
  T_IsInvertibleUnitalMagma_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_1052 v0
  = coe
      d_'8315''185''45'cong_976 (coe d_isInvertibleMagma_1024 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma._.∙-cong
d_'8729''45'cong_1054 ::
  T_IsInvertibleUnitalMagma_1012 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1054 v0
  = coe
      d_'8729''45'cong_188
      (coe d_isMagma_972 (coe d_isInvertibleMagma_1024 (coe v0)))
-- Algebra.Structures.IsInvertibleUnitalMagma._.∙-congʳ
d_'8729''45'cong'691'_1056 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1056 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1056 v7
du_'8729''45'cong'691'_1056 ::
  T_IsInvertibleUnitalMagma_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1056 v0
  = let v1 = d_isInvertibleMagma_1024 (coe v0) in
    coe
      (let v2 = d_isMagma_972 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsInvertibleUnitalMagma._.∙-congˡ
d_'8729''45'cong'737'_1058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1058 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1058 v7
du_'8729''45'cong'737'_1058 ::
  T_IsInvertibleUnitalMagma_1012 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1058 v0
  = let v1 = d_isInvertibleMagma_1024 (coe v0) in
    coe
      (let v2 = d_isMagma_972 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsInvertibleUnitalMagma.identityˡ
d_identity'737'_1060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_1012 -> AgdaAny -> AgdaAny
d_identity'737'_1060 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_1060 v7
du_identity'737'_1060 ::
  T_IsInvertibleUnitalMagma_1012 -> AgdaAny -> AgdaAny
du_identity'737'_1060 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_identity_1026 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma.identityʳ
d_identity'691'_1062 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_1012 -> AgdaAny -> AgdaAny
d_identity'691'_1062 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_1062 v7
du_identity'691'_1062 ::
  T_IsInvertibleUnitalMagma_1012 -> AgdaAny -> AgdaAny
du_identity'691'_1062 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_identity_1026 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma.isUnitalMagma
d_isUnitalMagma_1064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_1012 -> T_IsUnitalMagma_666
d_isUnitalMagma_1064 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isUnitalMagma_1064 v7
du_isUnitalMagma_1064 ::
  T_IsInvertibleUnitalMagma_1012 -> T_IsUnitalMagma_666
du_isUnitalMagma_1064 v0
  = coe
      C_constructor_706
      (coe d_isMagma_972 (coe d_isInvertibleMagma_1024 (coe v0)))
      (coe d_identity_1026 (coe v0))
-- Algebra.Structures.IsGroup
d_IsGroup_1074 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsGroup_1074
  = C_constructor_1164 T_IsMonoid_712
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsGroup.isMonoid
d_isMonoid_1088 :: T_IsGroup_1074 -> T_IsMonoid_712
d_isMonoid_1088 v0
  = case coe v0 of
      C_constructor_1164 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsGroup.inverse
d_inverse_1090 ::
  T_IsGroup_1074 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1090 v0
  = case coe v0 of
      C_constructor_1164 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsGroup.⁻¹-cong
d_'8315''185''45'cong_1092 ::
  T_IsGroup_1074 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_1092 v0
  = case coe v0 of
      C_constructor_1164 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsGroup._.assoc
d_assoc_1096 ::
  T_IsGroup_1074 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1096 v0
  = coe
      d_assoc_498 (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v0)))
-- Algebra.Structures.IsGroup._.identity
d_identity_1098 ::
  T_IsGroup_1074 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1098 v0
  = coe d_identity_724 (coe d_isMonoid_1088 (coe v0))
-- Algebra.Structures.IsGroup._.identityʳ
d_identity'691'_1100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1074 -> AgdaAny -> AgdaAny
d_identity'691'_1100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_1100 v7
du_identity'691'_1100 :: T_IsGroup_1074 -> AgdaAny -> AgdaAny
du_identity'691'_1100 v0
  = coe du_identity'691'_754 (coe d_isMonoid_1088 (coe v0))
-- Algebra.Structures.IsGroup._.identityˡ
d_identity'737'_1102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1074 -> AgdaAny -> AgdaAny
d_identity'737'_1102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_1102 v7
du_identity'737'_1102 :: T_IsGroup_1074 -> AgdaAny -> AgdaAny
du_identity'737'_1102 v0
  = coe du_identity'737'_752 (coe d_isMonoid_1088 (coe v0))
-- Algebra.Structures.IsGroup._.isEquivalence
d_isEquivalence_1104 ::
  T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1104 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v0))))
-- Algebra.Structures.IsGroup._.isMagma
d_isMagma_1106 :: T_IsGroup_1074 -> T_IsMagma_178
d_isMagma_1106 v0
  = coe
      d_isMagma_496
      (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v0)))
-- Algebra.Structures.IsGroup._.isPartialEquivalence
d_isPartialEquivalence_1108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1108 v7
du_isPartialEquivalence_1108 ::
  T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1108 v0
  = let v1 = d_isMonoid_1088 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.IsGroup._.isSemigroup
d_isSemigroup_1110 :: T_IsGroup_1074 -> T_IsSemigroup_488
d_isSemigroup_1110 v0
  = coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v0))
-- Algebra.Structures.IsGroup._.isUnitalMagma
d_isUnitalMagma_1112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1074 -> T_IsUnitalMagma_666
d_isUnitalMagma_1112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isUnitalMagma_1112 v7
du_isUnitalMagma_1112 :: T_IsGroup_1074 -> T_IsUnitalMagma_666
du_isUnitalMagma_1112 v0
  = coe du_isUnitalMagma_756 (coe d_isMonoid_1088 (coe v0))
-- Algebra.Structures.IsGroup._.refl
d_refl_1114 :: T_IsGroup_1074 -> AgdaAny -> AgdaAny
d_refl_1114 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v0)))))
-- Algebra.Structures.IsGroup._.reflexive
d_reflexive_1116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1116 v7
du_reflexive_1116 ::
  T_IsGroup_1074 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1116 v0
  = let v1 = d_isMonoid_1088 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_186 (coe v3)) v4)))
-- Algebra.Structures.IsGroup._.setoid
d_setoid_1118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1118 v7
du_setoid_1118 ::
  T_IsGroup_1074 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1118 v0
  = let v1 = d_isMonoid_1088 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe (coe du_setoid_202 (coe d_isMagma_496 (coe v2))))
-- Algebra.Structures.IsGroup._.sym
d_sym_1120 ::
  T_IsGroup_1074 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1120 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v0)))))
-- Algebra.Structures.IsGroup._.trans
d_trans_1122 ::
  T_IsGroup_1074 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1122 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v0)))))
-- Algebra.Structures.IsGroup._.∙-cong
d_'8729''45'cong_1124 ::
  T_IsGroup_1074 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1124 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v0))))
-- Algebra.Structures.IsGroup._.∙-congʳ
d_'8729''45'cong'691'_1126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1126 v7
du_'8729''45'cong'691'_1126 ::
  T_IsGroup_1074 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1126 v0
  = let v1 = d_isMonoid_1088 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsGroup._.∙-congˡ
d_'8729''45'cong'737'_1128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1128 v7
du_'8729''45'cong'737'_1128 ::
  T_IsGroup_1074 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1128 v0
  = let v1 = d_isMonoid_1088 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsGroup._\\_
d__'92''92'__1130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 -> AgdaAny -> AgdaAny -> AgdaAny
d__'92''92'__1130 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 v8 v9
  = du__'92''92'__1130 v4 v6 v8 v9
du__'92''92'__1130 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'92''92'__1130 v0 v1 v2 v3 = coe v0 (coe v1 v2) v3
-- Algebra.Structures.IsGroup._//_
d__'47''47'__1136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__1136 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 v8 v9
  = du__'47''47'__1136 v4 v6 v8 v9
du__'47''47'__1136 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__1136 v0 v1 v2 v3 = coe v0 v2 (coe v1 v3)
-- Algebra.Structures.IsGroup._-_
d__'45'__1142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 -> AgdaAny -> AgdaAny -> AgdaAny
d__'45'__1142 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 = du__'45'__1142 v4 v6
du__'45'__1142 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'45'__1142 v0 v1 = coe du__'47''47'__1136 (coe v0) (coe v1)
-- Algebra.Structures.IsGroup.inverseˡ
d_inverse'737'_1144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1074 -> AgdaAny -> AgdaAny
d_inverse'737'_1144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'737'_1144 v7
du_inverse'737'_1144 :: T_IsGroup_1074 -> AgdaAny -> AgdaAny
du_inverse'737'_1144 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_inverse_1090 (coe v0))
-- Algebra.Structures.IsGroup.inverseʳ
d_inverse'691'_1146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1074 -> AgdaAny -> AgdaAny
d_inverse'691'_1146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'691'_1146 v7
du_inverse'691'_1146 :: T_IsGroup_1074 -> AgdaAny -> AgdaAny
du_inverse'691'_1146 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_inverse_1090 (coe v0))
-- Algebra.Structures.IsGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_1152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_1152 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'737''45''8315''185'_1152 v4 v5 v6 v7
du_unique'737''45''8315''185'_1152 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_1152 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'id'8743'inv'691''8658'inv'737''45'unique_482
      (coe
         du_setoid_202
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v3)))))
      (coe v0) (coe v2) (coe v1)
      (coe
         d_'8729''45'cong_188
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v3)))))
      (coe
         d_assoc_498 (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v3))))
      (coe d_identity_724 (coe d_isMonoid_1088 (coe v3)))
      (coe du_inverse'691'_1146 (coe v3))
-- Algebra.Structures.IsGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_1158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_1158 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'691''45''8315''185'_1158 v4 v5 v6 v7
du_unique'691''45''8315''185'_1158 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_1158 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'id'8743'inv'737''8658'inv'691''45'unique_502
      (coe
         du_setoid_202
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v3)))))
      (coe v0) (coe v2) (coe v1)
      (coe
         d_'8729''45'cong_188
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v3)))))
      (coe
         d_assoc_498 (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v3))))
      (coe d_identity_724 (coe d_isMonoid_1088 (coe v3)))
      (coe du_inverse'737'_1144 (coe v3))
-- Algebra.Structures.IsGroup.isInvertibleMagma
d_isInvertibleMagma_1160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1074 -> T_IsInvertibleMagma_958
d_isInvertibleMagma_1160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleMagma_1160 v7
du_isInvertibleMagma_1160 ::
  T_IsGroup_1074 -> T_IsInvertibleMagma_958
du_isInvertibleMagma_1160 v0
  = coe
      C_constructor_1004
      (coe
         d_isMagma_496
         (coe d_isSemigroup_722 (coe d_isMonoid_1088 (coe v0))))
      (coe d_inverse_1090 (coe v0))
      (coe d_'8315''185''45'cong_1092 (coe v0))
-- Algebra.Structures.IsGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_1162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1074 -> T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_1162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleUnitalMagma_1162 v7
du_isInvertibleUnitalMagma_1162 ::
  T_IsGroup_1074 -> T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_1162 v0
  = coe
      C_constructor_1066 (coe du_isInvertibleMagma_1160 (coe v0))
      (coe d_identity_724 (coe d_isMonoid_1088 (coe v0)))
-- Algebra.Structures.IsAbelianGroup
d_IsAbelianGroup_1172 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsAbelianGroup_1172
  = C_constructor_1252 T_IsGroup_1074 (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsAbelianGroup.isGroup
d_isGroup_1184 :: T_IsAbelianGroup_1172 -> T_IsGroup_1074
d_isGroup_1184 v0
  = case coe v0 of
      C_constructor_1252 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsAbelianGroup.comm
d_comm_1186 ::
  T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_1186 v0
  = case coe v0 of
      C_constructor_1252 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsAbelianGroup._._//_
d__'47''47'__1190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__1190 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7
  = du__'47''47'__1190 v4 v6
du__'47''47'__1190 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__1190 v0 v1 = coe du__'47''47'__1136 (coe v0) (coe v1)
-- Algebra.Structures.IsAbelianGroup._.assoc
d_assoc_1192 ::
  T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1192 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe d_isMonoid_1088 (coe d_isGroup_1184 (coe v0))))
-- Algebra.Structures.IsAbelianGroup._.identity
d_identity_1194 ::
  T_IsAbelianGroup_1172 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1194 v0
  = coe
      d_identity_724 (coe d_isMonoid_1088 (coe d_isGroup_1184 (coe v0)))
-- Algebra.Structures.IsAbelianGroup._.identityʳ
d_identity'691'_1196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny
d_identity'691'_1196 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_1196 v7
du_identity'691'_1196 ::
  T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny
du_identity'691'_1196 v0
  = let v1 = d_isGroup_1184 (coe v0) in
    coe (coe du_identity'691'_754 (coe d_isMonoid_1088 (coe v1)))
-- Algebra.Structures.IsAbelianGroup._.identityˡ
d_identity'737'_1198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny
d_identity'737'_1198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_1198 v7
du_identity'737'_1198 ::
  T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny
du_identity'737'_1198 v0
  = let v1 = d_isGroup_1184 (coe v0) in
    coe (coe du_identity'737'_752 (coe d_isMonoid_1088 (coe v1)))
-- Algebra.Structures.IsAbelianGroup._.inverse
d_inverse_1200 ::
  T_IsAbelianGroup_1172 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1200 v0
  = coe d_inverse_1090 (coe d_isGroup_1184 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.inverseʳ
d_inverse'691'_1202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny
d_inverse'691'_1202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'691'_1202 v7
du_inverse'691'_1202 :: T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny
du_inverse'691'_1202 v0
  = coe du_inverse'691'_1146 (coe d_isGroup_1184 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.inverseˡ
d_inverse'737'_1204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny
d_inverse'737'_1204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'737'_1204 v7
du_inverse'737'_1204 :: T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny
du_inverse'737'_1204 v0
  = coe du_inverse'737'_1144 (coe d_isGroup_1184 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.isEquivalence
d_isEquivalence_1206 ::
  T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1206 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe d_isMonoid_1088 (coe d_isGroup_1184 (coe v0)))))
-- Algebra.Structures.IsAbelianGroup._.isInvertibleMagma
d_isInvertibleMagma_1208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 -> T_IsInvertibleMagma_958
d_isInvertibleMagma_1208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleMagma_1208 v7
du_isInvertibleMagma_1208 ::
  T_IsAbelianGroup_1172 -> T_IsInvertibleMagma_958
du_isInvertibleMagma_1208 v0
  = coe du_isInvertibleMagma_1160 (coe d_isGroup_1184 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_1210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 -> T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_1210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleUnitalMagma_1210 v7
du_isInvertibleUnitalMagma_1210 ::
  T_IsAbelianGroup_1172 -> T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_1210 v0
  = coe du_isInvertibleUnitalMagma_1162 (coe d_isGroup_1184 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.isMagma
d_isMagma_1212 :: T_IsAbelianGroup_1172 -> T_IsMagma_178
d_isMagma_1212 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe d_isMonoid_1088 (coe d_isGroup_1184 (coe v0))))
-- Algebra.Structures.IsAbelianGroup._.isMonoid
d_isMonoid_1214 :: T_IsAbelianGroup_1172 -> T_IsMonoid_712
d_isMonoid_1214 v0
  = coe d_isMonoid_1088 (coe d_isGroup_1184 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.isPartialEquivalence
d_isPartialEquivalence_1216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1216 v7
du_isPartialEquivalence_1216 ::
  T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1216 v0
  = let v1 = d_isGroup_1184 (coe v0) in
    coe
      (let v2 = d_isMonoid_1088 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe d_isEquivalence_186 (coe v4))))))
-- Algebra.Structures.IsAbelianGroup._.isSemigroup
d_isSemigroup_1218 :: T_IsAbelianGroup_1172 -> T_IsSemigroup_488
d_isSemigroup_1218 v0
  = coe
      d_isSemigroup_722
      (coe d_isMonoid_1088 (coe d_isGroup_1184 (coe v0)))
-- Algebra.Structures.IsAbelianGroup._.isUnitalMagma
d_isUnitalMagma_1220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 -> T_IsUnitalMagma_666
d_isUnitalMagma_1220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isUnitalMagma_1220 v7
du_isUnitalMagma_1220 ::
  T_IsAbelianGroup_1172 -> T_IsUnitalMagma_666
du_isUnitalMagma_1220 v0
  = let v1 = d_isGroup_1184 (coe v0) in
    coe (coe du_isUnitalMagma_756 (coe d_isMonoid_1088 (coe v1)))
-- Algebra.Structures.IsAbelianGroup._.refl
d_refl_1222 :: T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny
d_refl_1222 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe d_isMonoid_1088 (coe d_isGroup_1184 (coe v0))))))
-- Algebra.Structures.IsAbelianGroup._.reflexive
d_reflexive_1224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1224 v7
du_reflexive_1224 ::
  T_IsAbelianGroup_1172 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1224 v0
  = let v1 = d_isGroup_1184 (coe v0) in
    coe
      (let v2 = d_isMonoid_1088 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe d_isEquivalence_186 (coe v4)) v5))))
-- Algebra.Structures.IsAbelianGroup._.setoid
d_setoid_1226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1226 v7
du_setoid_1226 ::
  T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1226 v0
  = let v1 = d_isGroup_1184 (coe v0) in
    coe
      (let v2 = d_isMonoid_1088 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe (coe du_setoid_202 (coe d_isMagma_496 (coe v3)))))
-- Algebra.Structures.IsAbelianGroup._.sym
d_sym_1228 ::
  T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1228 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe d_isMonoid_1088 (coe d_isGroup_1184 (coe v0))))))
-- Algebra.Structures.IsAbelianGroup._.trans
d_trans_1230 ::
  T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1230 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe d_isMonoid_1088 (coe d_isGroup_1184 (coe v0))))))
-- Algebra.Structures.IsAbelianGroup._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_1232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_1232 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'691''45''8315''185'_1232 v4 v5 v6 v7
du_unique'691''45''8315''185'_1232 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_1232 v0 v1 v2 v3
  = coe
      du_unique'691''45''8315''185'_1158 (coe v0) (coe v1) (coe v2)
      (coe d_isGroup_1184 (coe v3))
-- Algebra.Structures.IsAbelianGroup._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_1234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_1234 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'737''45''8315''185'_1234 v4 v5 v6 v7
du_unique'737''45''8315''185'_1234 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_1234 v0 v1 v2 v3
  = coe
      du_unique'737''45''8315''185'_1152 (coe v0) (coe v1) (coe v2)
      (coe d_isGroup_1184 (coe v3))
-- Algebra.Structures.IsAbelianGroup._.⁻¹-cong
d_'8315''185''45'cong_1236 ::
  T_IsAbelianGroup_1172 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_1236 v0
  = coe d_'8315''185''45'cong_1092 (coe d_isGroup_1184 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.∙-cong
d_'8729''45'cong_1238 ::
  T_IsAbelianGroup_1172 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1238 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe d_isMonoid_1088 (coe d_isGroup_1184 (coe v0)))))
-- Algebra.Structures.IsAbelianGroup._.∙-congʳ
d_'8729''45'cong'691'_1240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1240 v7
du_'8729''45'cong'691'_1240 ::
  T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1240 v0
  = let v1 = d_isGroup_1184 (coe v0) in
    coe
      (let v2 = d_isMonoid_1088 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsAbelianGroup._.∙-congˡ
d_'8729''45'cong'737'_1242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1242 v7
du_'8729''45'cong'737'_1242 ::
  T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1242 v0
  = let v1 = d_isGroup_1184 (coe v0) in
    coe
      (let v2 = d_isMonoid_1088 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsAbelianGroup.isCommutativeMonoid
d_isCommutativeMonoid_1244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 -> T_IsCommutativeMonoid_764
d_isCommutativeMonoid_1244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMonoid_1244 v7
du_isCommutativeMonoid_1244 ::
  T_IsAbelianGroup_1172 -> T_IsCommutativeMonoid_764
du_isCommutativeMonoid_1244 v0
  = coe
      C_constructor_820
      (coe d_isMonoid_1088 (coe d_isGroup_1184 (coe v0)))
      (coe d_comm_1186 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.isCommutativeMagma
d_isCommutativeMagma_1248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_1248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMagma_1248 v7
du_isCommutativeMagma_1248 ::
  T_IsAbelianGroup_1172 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_1248 v0
  = let v1 = coe du_isCommutativeMonoid_1244 (coe v0) in
    coe
      (coe
         du_isCommutativeMagma_606
         (coe du_isCommutativeSemigroup_814 (coe v1)))
-- Algebra.Structures.IsAbelianGroup._.isCommutativeSemigroup
d_isCommutativeSemigroup_1250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1172 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeSemigroup_1250 v7
du_isCommutativeSemigroup_1250 ::
  T_IsAbelianGroup_1172 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1250 v0
  = coe
      du_isCommutativeSemigroup_814
      (coe du_isCommutativeMonoid_1244 (coe v0))
-- Algebra.Structures.IsNearSemiring
d_IsNearSemiring_1260 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsNearSemiring_1260
  = C_constructor_1334 T_IsMonoid_712
                       (AgdaAny ->
                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsNearSemiring.+-isMonoid
d_'43''45'isMonoid_1278 :: T_IsNearSemiring_1260 -> T_IsMonoid_712
d_'43''45'isMonoid_1278 v0
  = case coe v0 of
      C_constructor_1334 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearSemiring.*-cong
d_'42''45'cong_1280 ::
  T_IsNearSemiring_1260 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1280 v0
  = case coe v0 of
      C_constructor_1334 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearSemiring.*-assoc
d_'42''45'assoc_1282 ::
  T_IsNearSemiring_1260 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1282 v0
  = case coe v0 of
      C_constructor_1334 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearSemiring.distribʳ
d_distrib'691'_1284 ::
  T_IsNearSemiring_1260 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1284 v0
  = case coe v0 of
      C_constructor_1334 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearSemiring.zeroˡ
d_zero'737'_1286 :: T_IsNearSemiring_1260 -> AgdaAny -> AgdaAny
d_zero'737'_1286 v0
  = case coe v0 of
      C_constructor_1334 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearSemiring._.assoc
d_assoc_1290 ::
  T_IsNearSemiring_1260 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1290 v0
  = coe
      d_assoc_498
      (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_1278 (coe v0)))
-- Algebra.Structures.IsNearSemiring._.∙-cong
d_'8729''45'cong_1292 ::
  T_IsNearSemiring_1260 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1292 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_1278 (coe v0))))
-- Algebra.Structures.IsNearSemiring._.∙-congʳ
d_'8729''45'cong'691'_1294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1294 v7
du_'8729''45'cong'691'_1294 ::
  T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1294 v0
  = let v1 = d_'43''45'isMonoid_1278 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsNearSemiring._.∙-congˡ
d_'8729''45'cong'737'_1296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1296 v7
du_'8729''45'cong'737'_1296 ::
  T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1296 v0
  = let v1 = d_'43''45'isMonoid_1278 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsNearSemiring._.identity
d_identity_1298 ::
  T_IsNearSemiring_1260 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1298 v0
  = coe d_identity_724 (coe d_'43''45'isMonoid_1278 (coe v0))
-- Algebra.Structures.IsNearSemiring._.identityʳ
d_identity'691'_1300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsNearSemiring_1260 -> AgdaAny -> AgdaAny
d_identity'691'_1300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_1300 v7
du_identity'691'_1300 ::
  T_IsNearSemiring_1260 -> AgdaAny -> AgdaAny
du_identity'691'_1300 v0
  = coe du_identity'691'_754 (coe d_'43''45'isMonoid_1278 (coe v0))
-- Algebra.Structures.IsNearSemiring._.identityˡ
d_identity'737'_1302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsNearSemiring_1260 -> AgdaAny -> AgdaAny
d_identity'737'_1302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_1302 v7
du_identity'737'_1302 ::
  T_IsNearSemiring_1260 -> AgdaAny -> AgdaAny
du_identity'737'_1302 v0
  = coe du_identity'737'_752 (coe d_'43''45'isMonoid_1278 (coe v0))
-- Algebra.Structures.IsNearSemiring._.isMagma
d_isMagma_1304 :: T_IsNearSemiring_1260 -> T_IsMagma_178
d_isMagma_1304 v0
  = coe
      d_isMagma_496
      (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_1278 (coe v0)))
-- Algebra.Structures.IsNearSemiring._.isSemigroup
d_isSemigroup_1306 :: T_IsNearSemiring_1260 -> T_IsSemigroup_488
d_isSemigroup_1306 v0
  = coe d_isSemigroup_722 (coe d_'43''45'isMonoid_1278 (coe v0))
-- Algebra.Structures.IsNearSemiring._.isUnitalMagma
d_isUnitalMagma_1308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsNearSemiring_1260 -> T_IsUnitalMagma_666
d_isUnitalMagma_1308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isUnitalMagma_1308 v7
du_isUnitalMagma_1308 ::
  T_IsNearSemiring_1260 -> T_IsUnitalMagma_666
du_isUnitalMagma_1308 v0
  = coe du_isUnitalMagma_756 (coe d_'43''45'isMonoid_1278 (coe v0))
-- Algebra.Structures.IsNearSemiring._.isEquivalence
d_isEquivalence_1310 ::
  T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1310 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_1278 (coe v0))))
-- Algebra.Structures.IsNearSemiring._.isPartialEquivalence
d_isPartialEquivalence_1312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1312 v7
du_isPartialEquivalence_1312 ::
  T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1312 v0
  = let v1 = d_'43''45'isMonoid_1278 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.IsNearSemiring._.refl
d_refl_1314 :: T_IsNearSemiring_1260 -> AgdaAny -> AgdaAny
d_refl_1314 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_1278 (coe v0)))))
-- Algebra.Structures.IsNearSemiring._.reflexive
d_reflexive_1316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1260 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1316 v7
du_reflexive_1316 ::
  T_IsNearSemiring_1260 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1316 v0
  = let v1 = d_'43''45'isMonoid_1278 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_186 (coe v3)) v4)))
-- Algebra.Structures.IsNearSemiring._.setoid
d_setoid_1318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1318 v7
du_setoid_1318 ::
  T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1318 v0
  = let v1 = d_'43''45'isMonoid_1278 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe (coe du_setoid_202 (coe d_isMagma_496 (coe v2))))
-- Algebra.Structures.IsNearSemiring._.sym
d_sym_1320 ::
  T_IsNearSemiring_1260 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1320 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_1278 (coe v0)))))
-- Algebra.Structures.IsNearSemiring._.trans
d_trans_1322 ::
  T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1322 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_1278 (coe v0)))))
-- Algebra.Structures.IsNearSemiring.*-isMagma
d_'42''45'isMagma_1324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsNearSemiring_1260 -> T_IsMagma_178
d_'42''45'isMagma_1324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagma_1324 v7
du_'42''45'isMagma_1324 :: T_IsNearSemiring_1260 -> T_IsMagma_178
du_'42''45'isMagma_1324 v0
  = coe
      C_constructor_210
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_1278 (coe v0)))))
      (coe d_'42''45'cong_1280 (coe v0))
-- Algebra.Structures.IsNearSemiring.*-isSemigroup
d_'42''45'isSemigroup_1326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsNearSemiring_1260 -> T_IsSemigroup_488
d_'42''45'isSemigroup_1326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isSemigroup_1326 v7
du_'42''45'isSemigroup_1326 ::
  T_IsNearSemiring_1260 -> T_IsSemigroup_488
du_'42''45'isSemigroup_1326 v0
  = coe
      C_constructor_522 (coe du_'42''45'isMagma_1324 (coe v0))
      (coe d_'42''45'assoc_1282 (coe v0))
-- Algebra.Structures.IsNearSemiring._.∙-congʳ
d_'8729''45'cong'691'_1330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1330 v7
du_'8729''45'cong'691'_1330 ::
  T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1330 v0
  = let v1 = coe du_'42''45'isMagma_1324 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsNearSemiring._.∙-congˡ
d_'8729''45'cong'737'_1332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1332 v7
du_'8729''45'cong'737'_1332 ::
  T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1332 v0
  = let v1 = coe du_'42''45'isMagma_1324 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsSemiringWithoutOne
d_IsSemiringWithoutOne_1342 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemiringWithoutOne_1342
  = C_constructor_1430 T_IsCommutativeMonoid_764
                       (AgdaAny ->
                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1360 ::
  T_IsSemiringWithoutOne_1342 -> T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1360 v0
  = case coe v0 of
      C_constructor_1430 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutOne.*-cong
d_'42''45'cong_1362 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1362 v0
  = case coe v0 of
      C_constructor_1430 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutOne.*-assoc
d_'42''45'assoc_1364 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1364 v0
  = case coe v0 of
      C_constructor_1430 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutOne.distrib
d_distrib_1366 ::
  T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1366 v0
  = case coe v0 of
      C_constructor_1430 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutOne.zero
d_zero_1368 ::
  T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1368 v0
  = case coe v0 of
      C_constructor_1430 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutOne._.assoc
d_assoc_1372 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1372 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1360 (coe v0))))
-- Algebra.Structures.IsSemiringWithoutOne._.comm
d_comm_1374 ::
  T_IsSemiringWithoutOne_1342 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_1374 v0
  = coe d_comm_776 (coe d_'43''45'isCommutativeMonoid_1360 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne._.∙-cong
d_'8729''45'cong_1376 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1376 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1360 (coe v0)))))
-- Algebra.Structures.IsSemiringWithoutOne._.∙-congʳ
d_'8729''45'cong'691'_1378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1378 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1378 v7
du_'8729''45'cong'691'_1378 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1378 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1360 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsSemiringWithoutOne._.∙-congˡ
d_'8729''45'cong'737'_1380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1380 v7
du_'8729''45'cong'737'_1380 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1380 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1360 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsSemiringWithoutOne._.identity
d_identity_1382 ::
  T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1382 v0
  = coe
      d_identity_724
      (coe
         d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1360 (coe v0)))
-- Algebra.Structures.IsSemiringWithoutOne._.identityʳ
d_identity'691'_1384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1342 -> AgdaAny -> AgdaAny
d_identity'691'_1384 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_1384 v7
du_identity'691'_1384 ::
  T_IsSemiringWithoutOne_1342 -> AgdaAny -> AgdaAny
du_identity'691'_1384 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1360 (coe v0) in
    coe (coe du_identity'691'_754 (coe d_isMonoid_774 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutOne._.identityˡ
d_identity'737'_1386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1342 -> AgdaAny -> AgdaAny
d_identity'737'_1386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_1386 v7
du_identity'737'_1386 ::
  T_IsSemiringWithoutOne_1342 -> AgdaAny -> AgdaAny
du_identity'737'_1386 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1360 (coe v0) in
    coe (coe du_identity'737'_752 (coe d_isMonoid_774 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutOne._.isCommutativeMagma
d_isCommutativeMagma_1388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1342 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_1388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMagma_1388 v7
du_isCommutativeMagma_1388 ::
  T_IsSemiringWithoutOne_1342 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_1388 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1360 (coe v0) in
    coe
      (coe
         du_isCommutativeMagma_606
         (coe du_isCommutativeSemigroup_814 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutOne._.isCommutativeSemigroup
d_isCommutativeSemigroup_1390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1342 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeSemigroup_1390 v7
du_isCommutativeSemigroup_1390 ::
  T_IsSemiringWithoutOne_1342 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1390 v0
  = coe
      du_isCommutativeSemigroup_814
      (coe d_'43''45'isCommutativeMonoid_1360 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne._.isMonoid
d_isMonoid_1392 :: T_IsSemiringWithoutOne_1342 -> T_IsMonoid_712
d_isMonoid_1392 v0
  = coe
      d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1360 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne._.isEquivalence
d_isEquivalence_1394 ::
  T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1394 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1360 (coe v0)))))
-- Algebra.Structures.IsSemiringWithoutOne._.setoid
d_setoid_1396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1396 v7
du_setoid_1396 ::
  T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1396 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1360 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe (coe du_setoid_202 (coe d_isMagma_496 (coe v3)))))
-- Algebra.Structures.IsSemiringWithoutOne._.isPartialEquivalence
d_isPartialEquivalence_1400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1400 v7
du_isPartialEquivalence_1400 ::
  T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1400 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe d_'43''45'isCommutativeMonoid_1360 (coe v0))))))
-- Algebra.Structures.IsSemiringWithoutOne._.refl
d_refl_1402 :: T_IsSemiringWithoutOne_1342 -> AgdaAny -> AgdaAny
d_refl_1402 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe d_'43''45'isCommutativeMonoid_1360 (coe v0))))))
-- Algebra.Structures.IsSemiringWithoutOne._.reflexive
d_reflexive_1404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1404 v7
du_reflexive_1404 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1404 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe d_'43''45'isCommutativeMonoid_1360 (coe v0))))))
      v1
-- Algebra.Structures.IsSemiringWithoutOne._.sym
d_sym_1406 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1406 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe d_'43''45'isCommutativeMonoid_1360 (coe v0))))))
-- Algebra.Structures.IsSemiringWithoutOne._.trans
d_trans_1408 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1408 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe d_'43''45'isCommutativeMonoid_1360 (coe v0))))))
-- Algebra.Structures.IsSemiringWithoutOne.*-isMagma
d_'42''45'isMagma_1410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1342 -> T_IsMagma_178
d_'42''45'isMagma_1410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagma_1410 v7
du_'42''45'isMagma_1410 ::
  T_IsSemiringWithoutOne_1342 -> T_IsMagma_178
du_'42''45'isMagma_1410 v0
  = coe
      C_constructor_210
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe d_'43''45'isCommutativeMonoid_1360 (coe v0))))))
      (coe d_'42''45'cong_1362 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_1412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1342 -> T_IsSemigroup_488
d_'42''45'isSemigroup_1412 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isSemigroup_1412 v7
du_'42''45'isSemigroup_1412 ::
  T_IsSemiringWithoutOne_1342 -> T_IsSemigroup_488
du_'42''45'isSemigroup_1412 v0
  = coe
      C_constructor_522 (coe du_'42''45'isMagma_1410 (coe v0))
      (coe d_'42''45'assoc_1364 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne._.∙-congʳ
d_'8729''45'cong'691'_1416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1416 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1416 v7
du_'8729''45'cong'691'_1416 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1416 v0
  = let v1 = coe du_'42''45'isMagma_1410 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsSemiringWithoutOne._.∙-congˡ
d_'8729''45'cong'737'_1418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1418 v7
du_'8729''45'cong'737'_1418 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1418 v0
  = let v1 = coe du_'42''45'isMagma_1410 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsSemiringWithoutOne.distribˡ
d_distrib'737'_1420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_distrib'737'_1420 v7
du_distrib'737'_1420 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1420 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_distrib_1366 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne.distribʳ
d_distrib'691'_1422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_distrib'691'_1422 v7
du_distrib'691'_1422 ::
  T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1422 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_distrib_1366 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne.zeroˡ
d_zero'737'_1424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1342 -> AgdaAny -> AgdaAny
d_zero'737'_1424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_zero'737'_1424 v7
du_zero'737'_1424 ::
  T_IsSemiringWithoutOne_1342 -> AgdaAny -> AgdaAny
du_zero'737'_1424 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_zero_1368 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne.zeroʳ
d_zero'691'_1426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1342 -> AgdaAny -> AgdaAny
d_zero'691'_1426 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_zero'691'_1426 v7
du_zero'691'_1426 ::
  T_IsSemiringWithoutOne_1342 -> AgdaAny -> AgdaAny
du_zero'691'_1426 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_zero_1368 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne.isNearSemiring
d_isNearSemiring_1428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1342 -> T_IsNearSemiring_1260
d_isNearSemiring_1428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiring_1428 v7
du_isNearSemiring_1428 ::
  T_IsSemiringWithoutOne_1342 -> T_IsNearSemiring_1260
du_isNearSemiring_1428 v0
  = coe
      C_constructor_1334
      (coe
         d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1360 (coe v0)))
      (coe d_'42''45'cong_1362 (coe v0))
      (coe d_'42''45'assoc_1364 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_distrib_1366 (coe v0)))
      (coe du_zero'737'_1424 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne
d_IsCommutativeSemiringWithoutOne_1438 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsCommutativeSemiringWithoutOne_1438
  = C_constructor_1526 T_IsSemiringWithoutOne_1342
                       (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeSemiringWithoutOne.isSemiringWithoutOne
d_isSemiringWithoutOne_1450 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_1450 v0
  = case coe v0 of
      C_constructor_1526 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemiringWithoutOne.*-comm
d_'42''45'comm_1452 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_1452 v0
  = case coe v0 of
      C_constructor_1526 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.*-assoc
d_'42''45'assoc_1456 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1456 v0
  = coe
      d_'42''45'assoc_1364 (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.*-cong
d_'42''45'cong_1458 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1458 v0
  = coe
      d_'42''45'cong_1362 (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.∙-congʳ
d_'8729''45'cong'691'_1460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1460 v7
du_'8729''45'cong'691'_1460 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1460 v0
  = let v1 = d_isSemiringWithoutOne_1450 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isMagma_1410 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.∙-congˡ
d_'8729''45'cong'737'_1462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1462 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1462 v7
du_'8729''45'cong'737'_1462 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1462 v0
  = let v1 = d_isSemiringWithoutOne_1450 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isMagma_1410 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.*-isMagma
d_'42''45'isMagma_1464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeSemiringWithoutOne_1438 -> T_IsMagma_178
d_'42''45'isMagma_1464 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagma_1464 v7
du_'42''45'isMagma_1464 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> T_IsMagma_178
du_'42''45'isMagma_1464 v0
  = coe
      du_'42''45'isMagma_1410 (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.*-isSemigroup
d_'42''45'isSemigroup_1466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 -> T_IsSemigroup_488
d_'42''45'isSemigroup_1466 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isSemigroup_1466 v7
du_'42''45'isSemigroup_1466 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> T_IsSemigroup_488
du_'42''45'isSemigroup_1466 v0
  = coe
      du_'42''45'isSemigroup_1412
      (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.assoc
d_assoc_1468 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1468 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774
            (coe
               d_'43''45'isCommutativeMonoid_1360
               (coe d_isSemiringWithoutOne_1450 (coe v0)))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.comm
d_comm_1470 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_1470 v0
  = coe
      d_comm_776
      (coe
         d_'43''45'isCommutativeMonoid_1360
         (coe d_isSemiringWithoutOne_1450 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.∙-cong
d_'8729''45'cong_1472 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1472 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1360
                  (coe d_isSemiringWithoutOne_1450 (coe v0))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.∙-congʳ
d_'8729''45'cong'691'_1474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1474 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1474 v7
du_'8729''45'cong'691'_1474 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1474 v0
  = let v1 = d_isSemiringWithoutOne_1450 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1360 (coe v1) in
       coe
         (let v3 = d_isMonoid_774 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.∙-congˡ
d_'8729''45'cong'737'_1476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1476 v7
du_'8729''45'cong'737'_1476 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1476 v0
  = let v1 = d_isSemiringWithoutOne_1450 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1360 (coe v1) in
       coe
         (let v3 = d_isMonoid_774 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.identity
d_identity_1478 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1478 v0
  = coe
      d_identity_724
      (coe
         d_isMonoid_774
         (coe
            d_'43''45'isCommutativeMonoid_1360
            (coe d_isSemiringWithoutOne_1450 (coe v0))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.identityʳ
d_identity'691'_1480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 -> AgdaAny -> AgdaAny
d_identity'691'_1480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_1480 v7
du_identity'691'_1480 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> AgdaAny -> AgdaAny
du_identity'691'_1480 v0
  = let v1 = d_isSemiringWithoutOne_1450 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1360 (coe v1) in
       coe (coe du_identity'691'_754 (coe d_isMonoid_774 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.identityˡ
d_identity'737'_1482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 -> AgdaAny -> AgdaAny
d_identity'737'_1482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_1482 v7
du_identity'737'_1482 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> AgdaAny -> AgdaAny
du_identity'737'_1482 v0
  = let v1 = d_isSemiringWithoutOne_1450 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1360 (coe v1) in
       coe (coe du_identity'737'_752 (coe d_isMonoid_774 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isCommutativeMagma
d_isCommutativeMagma_1484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_1484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMagma_1484 v7
du_isCommutativeMagma_1484 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_1484 v0
  = let v1 = d_isSemiringWithoutOne_1450 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1360 (coe v1) in
       coe
         (coe
            du_isCommutativeMagma_606
            (coe du_isCommutativeSemigroup_814 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1486 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1486 v0
  = coe
      d_'43''45'isCommutativeMonoid_1360
      (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isCommutativeSemigroup
d_isCommutativeSemigroup_1488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 ->
  T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1488 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeSemigroup_1488 v7
du_isCommutativeSemigroup_1488 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1488 v0
  = let v1 = d_isSemiringWithoutOne_1450 (coe v0) in
    coe
      (coe
         du_isCommutativeSemigroup_814
         (coe d_'43''45'isCommutativeMonoid_1360 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isMonoid
d_isMonoid_1490 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> T_IsMonoid_712
d_isMonoid_1490 v0
  = coe
      d_isMonoid_774
      (coe
         d_'43''45'isCommutativeMonoid_1360
         (coe d_isSemiringWithoutOne_1450 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.distrib
d_distrib_1492 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1492 v0
  = coe d_distrib_1366 (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.distribʳ
d_distrib'691'_1494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_distrib'691'_1494 v7
du_distrib'691'_1494 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1494 v0
  = coe
      du_distrib'691'_1422 (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.distribˡ
d_distrib'737'_1496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_distrib'737'_1496 v7
du_distrib'737'_1496 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1496 v0
  = coe
      du_distrib'737'_1420 (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isEquivalence
d_isEquivalence_1498 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1498 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1360
                  (coe d_isSemiringWithoutOne_1450 (coe v0))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isNearSemiring
d_isNearSemiring_1500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 -> T_IsNearSemiring_1260
d_isNearSemiring_1500 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiring_1500 v7
du_isNearSemiring_1500 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> T_IsNearSemiring_1260
du_isNearSemiring_1500 v0
  = coe
      du_isNearSemiring_1428 (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isPartialEquivalence
d_isPartialEquivalence_1502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1502 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1502 v7
du_isPartialEquivalence_1502 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1502 v0
  = let v1 = d_isSemiringWithoutOne_1450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe
            d_isEquivalence_186
            (coe
               d_isMagma_496
               (coe
                  d_isSemigroup_722
                  (coe
                     d_isMonoid_774
                     (coe d_'43''45'isCommutativeMonoid_1360 (coe v1)))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.refl
d_refl_1504 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> AgdaAny -> AgdaAny
d_refl_1504 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1360
                     (coe d_isSemiringWithoutOne_1450 (coe v0)))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.reflexive
d_reflexive_1506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1506 v7
du_reflexive_1506 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1506 v0
  = let v1 = d_isSemiringWithoutOne_1450 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe
              d_isEquivalence_186
              (coe
                 d_isMagma_496
                 (coe
                    d_isSemigroup_722
                    (coe
                       d_isMonoid_774
                       (coe d_'43''45'isCommutativeMonoid_1360 (coe v1))))))
           v2)
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.setoid
d_setoid_1508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1508 v7
du_setoid_1508 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1508 v0
  = let v1 = d_isSemiringWithoutOne_1450 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1360 (coe v1) in
       coe
         (let v3 = d_isMonoid_774 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe (coe du_setoid_202 (coe d_isMagma_496 (coe v4))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.sym
d_sym_1510 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1510 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1360
                     (coe d_isSemiringWithoutOne_1450 (coe v0)))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.trans
d_trans_1512 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1512 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1360
                     (coe d_isSemiringWithoutOne_1450 (coe v0)))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.zero
d_zero_1514 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1514 v0
  = coe d_zero_1368 (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.zeroʳ
d_zero'691'_1516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 -> AgdaAny -> AgdaAny
d_zero'691'_1516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_zero'691'_1516 v7
du_zero'691'_1516 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> AgdaAny -> AgdaAny
du_zero'691'_1516 v0
  = coe du_zero'691'_1426 (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.zeroˡ
d_zero'737'_1518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 -> AgdaAny -> AgdaAny
d_zero'737'_1518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_zero'737'_1518 v7
du_zero'737'_1518 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> AgdaAny -> AgdaAny
du_zero'737'_1518 v0
  = coe du_zero'737'_1424 (coe d_isSemiringWithoutOne_1450 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_1520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 ->
  T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_1520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      v7
  = du_'42''45'isCommutativeSemigroup_1520 v7
du_'42''45'isCommutativeSemigroup_1520 ::
  T_IsCommutativeSemiringWithoutOne_1438 ->
  T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_1520 v0
  = coe
      C_constructor_608
      (coe
         du_'42''45'isSemigroup_1412
         (coe d_isSemiringWithoutOne_1450 (coe v0)))
      (coe d_'42''45'comm_1452 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isCommutativeMagma
d_isCommutativeMagma_1524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1438 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_1524 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMagma_1524 v7
du_isCommutativeMagma_1524 ::
  T_IsCommutativeSemiringWithoutOne_1438 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_1524 v0
  = coe
      du_isCommutativeMagma_606
      (coe du_'42''45'isCommutativeSemigroup_1520 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_1536 a0 a1 a2 a3 a4 a5 a6 a7
  = ()
data T_IsSemiringWithoutAnnihilatingZero_1536
  = C_constructor_1630 T_IsCommutativeMonoid_764
                       (AgdaAny ->
                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1556 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1556 v0
  = case coe v0 of
      C_constructor_1630 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_1558 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1558 v0
  = case coe v0 of
      C_constructor_1630 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_1560 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1560 v0
  = case coe v0 of
      C_constructor_1630 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_1562 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1562 v0
  = case coe v0 of
      C_constructor_1630 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_1564 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1564 v0
  = case coe v0 of
      C_constructor_1630 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.distribˡ
d_distrib'737'_1566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1566 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_1566 v8
du_distrib'737'_1566 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1566 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_distrib_1564 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.distribʳ
d_distrib'691'_1568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1568 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_1568 v8
du_distrib'691'_1568 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1568 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_distrib_1564 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.assoc
d_assoc_1572 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1572 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1556 (coe v0))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.comm
d_comm_1574 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_1574 v0
  = coe d_comm_776 (coe d_'43''45'isCommutativeMonoid_1556 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.∙-cong
d_'8729''45'cong_1576 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1576 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1556 (coe v0)))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.∙-congʳ
d_'8729''45'cong'691'_1578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1578 v8
du_'8729''45'cong'691'_1578 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1578 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1556 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.∙-congˡ
d_'8729''45'cong'737'_1580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1580 v8
du_'8729''45'cong'737'_1580 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1580 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1556 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identity
d_identity_1582 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1582 v0
  = coe
      d_identity_724
      (coe
         d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1556 (coe v0)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identityʳ
d_identity'691'_1584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 -> AgdaAny -> AgdaAny
d_identity'691'_1584 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1584 v8
du_identity'691'_1584 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> AgdaAny -> AgdaAny
du_identity'691'_1584 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1556 (coe v0) in
    coe (coe du_identity'691'_754 (coe d_isMonoid_774 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identityˡ
d_identity'737'_1586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 -> AgdaAny -> AgdaAny
d_identity'737'_1586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1586 v8
du_identity'737'_1586 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> AgdaAny -> AgdaAny
du_identity'737'_1586 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1556 (coe v0) in
    coe (coe du_identity'737'_752 (coe d_isMonoid_774 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isCommutativeMagma
d_isCommutativeMagma_1588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  T_IsCommutativeMagma_214
d_isCommutativeMagma_1588 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1588 v8
du_isCommutativeMagma_1588 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  T_IsCommutativeMagma_214
du_isCommutativeMagma_1588 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1556 (coe v0) in
    coe
      (coe
         du_isCommutativeMagma_606
         (coe du_isCommutativeSemigroup_814 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isCommutativeSemigroup
d_isCommutativeSemigroup_1590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1590 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_1590 v8
du_isCommutativeSemigroup_1590 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1590 v0
  = coe
      du_isCommutativeSemigroup_814
      (coe d_'43''45'isCommutativeMonoid_1556 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isMagma
d_isMagma_1592 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> T_IsMagma_178
d_isMagma_1592 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1556 (coe v0))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isMonoid
d_isMonoid_1594 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> T_IsMonoid_712
d_isMonoid_1594 v0
  = coe
      d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1556 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isSemigroup
d_isSemigroup_1596 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> T_IsSemigroup_488
d_isSemigroup_1596 v0
  = coe
      d_isSemigroup_722
      (coe
         d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1556 (coe v0)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isUnitalMagma
d_isUnitalMagma_1598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 -> T_IsUnitalMagma_666
d_isUnitalMagma_1598 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_1598 v8
du_isUnitalMagma_1598 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> T_IsUnitalMagma_666
du_isUnitalMagma_1598 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1556 (coe v0) in
    coe (coe du_isUnitalMagma_756 (coe d_isMonoid_774 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isEquivalence
d_isEquivalence_1600 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1600 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774 (coe d_'43''45'isCommutativeMonoid_1556 (coe v0)))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isPartialEquivalence
d_isPartialEquivalence_1602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1602 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1602 v8
du_isPartialEquivalence_1602 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1602 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1556 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe d_isEquivalence_186 (coe v4))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.refl
d_refl_1604 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> AgdaAny -> AgdaAny
d_refl_1604 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe d_'43''45'isCommutativeMonoid_1556 (coe v0))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.reflexive
d_reflexive_1606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1606 v8
du_reflexive_1606 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1606 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1556 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe d_isEquivalence_186 (coe v4)) v5))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.setoid
d_setoid_1608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1608 v8
du_setoid_1608 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1608 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1556 (coe v0) in
    coe
      (let v2 = d_isMonoid_774 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe (coe du_setoid_202 (coe d_isMagma_496 (coe v3)))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.sym
d_sym_1610 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1610 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe d_'43''45'isCommutativeMonoid_1556 (coe v0))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.trans
d_trans_1612 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1612 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe d_'43''45'isCommutativeMonoid_1556 (coe v0))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-isMagma
d_'42''45'isMagma_1614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 -> T_IsMagma_178
d_'42''45'isMagma_1614 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_1614 v8
du_'42''45'isMagma_1614 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> T_IsMagma_178
du_'42''45'isMagma_1614 v0
  = coe
      C_constructor_210
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe d_'43''45'isCommutativeMonoid_1556 (coe v0))))))
      (coe d_'42''45'cong_1558 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-isSemigroup
d_'42''45'isSemigroup_1616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 -> T_IsSemigroup_488
d_'42''45'isSemigroup_1616 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_1616 v8
du_'42''45'isSemigroup_1616 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> T_IsSemigroup_488
du_'42''45'isSemigroup_1616 v0
  = coe
      C_constructor_522 (coe du_'42''45'isMagma_1614 (coe v0))
      (coe d_'42''45'assoc_1560 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-isMonoid
d_'42''45'isMonoid_1618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 -> T_IsMonoid_712
d_'42''45'isMonoid_1618 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_1618 v8
du_'42''45'isMonoid_1618 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> T_IsMonoid_712
du_'42''45'isMonoid_1618 v0
  = coe
      C_constructor_758 (coe du_'42''45'isSemigroup_1616 (coe v0))
      (coe d_'42''45'identity_1562 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.∙-congʳ
d_'8729''45'cong'691'_1622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1622 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1622 v8
du_'8729''45'cong'691'_1622 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1622 v0
  = let v1 = coe du_'42''45'isMonoid_1618 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.∙-congˡ
d_'8729''45'cong'737'_1624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1624 v8
du_'8729''45'cong'737'_1624 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1624 v0
  = let v1 = coe du_'42''45'isMonoid_1618 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identityʳ
d_identity'691'_1626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 -> AgdaAny -> AgdaAny
d_identity'691'_1626 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1626 v8
du_identity'691'_1626 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> AgdaAny -> AgdaAny
du_identity'691'_1626 v0
  = coe du_identity'691'_754 (coe du_'42''45'isMonoid_1618 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identityˡ
d_identity'737'_1628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1536 -> AgdaAny -> AgdaAny
d_identity'737'_1628 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1628 v8
du_identity'737'_1628 ::
  T_IsSemiringWithoutAnnihilatingZero_1536 -> AgdaAny -> AgdaAny
du_identity'737'_1628 v0
  = coe du_identity'737'_752 (coe du_'42''45'isMonoid_1618 (coe v0))
-- Algebra.Structures.IsSemiring
d_IsSemiring_1640 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsSemiring_1640
  = C_constructor_1740 T_IsSemiringWithoutAnnihilatingZero_1536
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1654 ::
  T_IsSemiring_1640 -> T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_1654 v0
  = case coe v0 of
      C_constructor_1740 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiring.zero
d_zero_1656 ::
  T_IsSemiring_1640 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1656 v0
  = case coe v0 of
      C_constructor_1740 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiring._.*-assoc
d_'42''45'assoc_1660 ::
  T_IsSemiring_1640 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1660 v0
  = coe
      d_'42''45'assoc_1560
      (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))
-- Algebra.Structures.IsSemiring._.*-cong
d_'42''45'cong_1662 ::
  T_IsSemiring_1640 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1662 v0
  = coe
      d_'42''45'cong_1558
      (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))
-- Algebra.Structures.IsSemiring._.∙-congʳ
d_'8729''45'cong'691'_1664 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1640 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1664 v8
du_'8729''45'cong'691'_1664 ::
  T_IsSemiring_1640 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1664 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isMonoid_1618 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsSemiring._.∙-congˡ
d_'8729''45'cong'737'_1666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1640 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1666 v8
du_'8729''45'cong'737'_1666 ::
  T_IsSemiring_1640 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1666 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isMonoid_1618 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsSemiring._.*-identity
d_'42''45'identity_1668 ::
  T_IsSemiring_1640 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1668 v0
  = coe
      d_'42''45'identity_1562
      (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))
-- Algebra.Structures.IsSemiring._.identityʳ
d_identity'691'_1670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> AgdaAny -> AgdaAny
d_identity'691'_1670 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1670 v8
du_identity'691'_1670 :: T_IsSemiring_1640 -> AgdaAny -> AgdaAny
du_identity'691'_1670 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (coe du_identity'691'_754 (coe du_'42''45'isMonoid_1618 (coe v1)))
-- Algebra.Structures.IsSemiring._.identityˡ
d_identity'737'_1672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> AgdaAny -> AgdaAny
d_identity'737'_1672 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1672 v8
du_identity'737'_1672 :: T_IsSemiring_1640 -> AgdaAny -> AgdaAny
du_identity'737'_1672 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (coe du_identity'737'_752 (coe du_'42''45'isMonoid_1618 (coe v1)))
-- Algebra.Structures.IsSemiring._.*-isMagma
d_'42''45'isMagma_1674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> T_IsMagma_178
d_'42''45'isMagma_1674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_1674 v8
du_'42''45'isMagma_1674 :: T_IsSemiring_1640 -> T_IsMagma_178
du_'42''45'isMagma_1674 v0
  = coe
      du_'42''45'isMagma_1614
      (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))
-- Algebra.Structures.IsSemiring._.*-isMonoid
d_'42''45'isMonoid_1676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> T_IsMonoid_712
d_'42''45'isMonoid_1676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_1676 v8
du_'42''45'isMonoid_1676 :: T_IsSemiring_1640 -> T_IsMonoid_712
du_'42''45'isMonoid_1676 v0
  = coe
      du_'42''45'isMonoid_1618
      (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))
-- Algebra.Structures.IsSemiring._.*-isSemigroup
d_'42''45'isSemigroup_1678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> T_IsSemigroup_488
d_'42''45'isSemigroup_1678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_1678 v8
du_'42''45'isSemigroup_1678 ::
  T_IsSemiring_1640 -> T_IsSemigroup_488
du_'42''45'isSemigroup_1678 v0
  = coe
      du_'42''45'isSemigroup_1616
      (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))
-- Algebra.Structures.IsSemiring._.assoc
d_assoc_1680 ::
  T_IsSemiring_1640 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1680 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774
            (coe
               d_'43''45'isCommutativeMonoid_1556
               (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0)))))
-- Algebra.Structures.IsSemiring._.comm
d_comm_1682 :: T_IsSemiring_1640 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_1682 v0
  = coe
      d_comm_776
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0)))
-- Algebra.Structures.IsSemiring._.∙-cong
d_'8729''45'cong_1684 ::
  T_IsSemiring_1640 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1684 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1556
                  (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))))))
-- Algebra.Structures.IsSemiring._.∙-congʳ
d_'8729''45'cong'691'_1686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1640 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1686 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1686 v8
du_'8729''45'cong'691'_1686 ::
  T_IsSemiring_1640 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1686 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1556 (coe v1) in
       coe
         (let v3 = d_isMonoid_774 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsSemiring._.∙-congˡ
d_'8729''45'cong'737'_1688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1640 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1688 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1688 v8
du_'8729''45'cong'737'_1688 ::
  T_IsSemiring_1640 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1688 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1556 (coe v1) in
       coe
         (let v3 = d_isMonoid_774 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsSemiring._.identity
d_identity_1690 ::
  T_IsSemiring_1640 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1690 v0
  = coe
      d_identity_724
      (coe
         d_isMonoid_774
         (coe
            d_'43''45'isCommutativeMonoid_1556
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))))
-- Algebra.Structures.IsSemiring._.identityʳ
d_identity'691'_1692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> AgdaAny -> AgdaAny
d_identity'691'_1692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1692 v8
du_identity'691'_1692 :: T_IsSemiring_1640 -> AgdaAny -> AgdaAny
du_identity'691'_1692 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1556 (coe v1) in
       coe (coe du_identity'691'_754 (coe d_isMonoid_774 (coe v2))))
-- Algebra.Structures.IsSemiring._.identityˡ
d_identity'737'_1694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> AgdaAny -> AgdaAny
d_identity'737'_1694 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1694 v8
du_identity'737'_1694 :: T_IsSemiring_1640 -> AgdaAny -> AgdaAny
du_identity'737'_1694 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1556 (coe v1) in
       coe (coe du_identity'737'_752 (coe d_isMonoid_774 (coe v2))))
-- Algebra.Structures.IsSemiring._.isCommutativeMagma
d_isCommutativeMagma_1696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_1696 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1696 v8
du_isCommutativeMagma_1696 ::
  T_IsSemiring_1640 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_1696 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1556 (coe v1) in
       coe
         (coe
            du_isCommutativeMagma_606
            (coe du_isCommutativeSemigroup_814 (coe v2))))
-- Algebra.Structures.IsSemiring._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1698 ::
  T_IsSemiring_1640 -> T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1698 v0
  = coe
      d_'43''45'isCommutativeMonoid_1556
      (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))
-- Algebra.Structures.IsSemiring._.isCommutativeSemigroup
d_isCommutativeSemigroup_1700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsSemiring_1640 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_1700 v8
du_isCommutativeSemigroup_1700 ::
  T_IsSemiring_1640 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1700 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (coe
         du_isCommutativeSemigroup_814
         (coe d_'43''45'isCommutativeMonoid_1556 (coe v1)))
-- Algebra.Structures.IsSemiring._.isMagma
d_isMagma_1702 :: T_IsSemiring_1640 -> T_IsMagma_178
d_isMagma_1702 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774
            (coe
               d_'43''45'isCommutativeMonoid_1556
               (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0)))))
-- Algebra.Structures.IsSemiring._.isMonoid
d_isMonoid_1704 :: T_IsSemiring_1640 -> T_IsMonoid_712
d_isMonoid_1704 v0
  = coe
      d_isMonoid_774
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0)))
-- Algebra.Structures.IsSemiring._.isSemigroup
d_isSemigroup_1706 :: T_IsSemiring_1640 -> T_IsSemigroup_488
d_isSemigroup_1706 v0
  = coe
      d_isSemigroup_722
      (coe
         d_isMonoid_774
         (coe
            d_'43''45'isCommutativeMonoid_1556
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))))
-- Algebra.Structures.IsSemiring._.isUnitalMagma
d_isUnitalMagma_1708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> T_IsUnitalMagma_666
d_isUnitalMagma_1708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_1708 v8
du_isUnitalMagma_1708 :: T_IsSemiring_1640 -> T_IsUnitalMagma_666
du_isUnitalMagma_1708 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1556 (coe v1) in
       coe (coe du_isUnitalMagma_756 (coe d_isMonoid_774 (coe v2))))
-- Algebra.Structures.IsSemiring._.distrib
d_distrib_1710 ::
  T_IsSemiring_1640 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1710 v0
  = coe
      d_distrib_1564
      (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))
-- Algebra.Structures.IsSemiring._.distribʳ
d_distrib'691'_1712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1640 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_1712 v8
du_distrib'691'_1712 ::
  T_IsSemiring_1640 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1712 v0
  = coe
      du_distrib'691'_1568
      (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))
-- Algebra.Structures.IsSemiring._.distribˡ
d_distrib'737'_1714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1640 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_1714 v8
du_distrib'737'_1714 ::
  T_IsSemiring_1640 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1714 v0
  = coe
      du_distrib'737'_1566
      (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))
-- Algebra.Structures.IsSemiring._.isEquivalence
d_isEquivalence_1716 ::
  T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1716 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1556
                  (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0))))))
-- Algebra.Structures.IsSemiring._.isPartialEquivalence
d_isPartialEquivalence_1718 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1718 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1718 v8
du_isPartialEquivalence_1718 ::
  T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1718 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1556 (coe v1) in
       coe
         (let v3 = d_isMonoid_774 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                     (coe d_isEquivalence_186 (coe v5)))))))
-- Algebra.Structures.IsSemiring._.refl
d_refl_1720 :: T_IsSemiring_1640 -> AgdaAny -> AgdaAny
d_refl_1720 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0)))))))
-- Algebra.Structures.IsSemiring._.reflexive
d_reflexive_1722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1640 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1722 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1722 v8
du_reflexive_1722 ::
  T_IsSemiring_1640 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1722 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1556 (coe v1) in
       coe
         (let v3 = d_isMonoid_774 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                       (coe d_isEquivalence_186 (coe v5)) v6)))))
-- Algebra.Structures.IsSemiring._.setoid
d_setoid_1724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1724 v8
du_setoid_1724 ::
  T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1724 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1556 (coe v1) in
       coe
         (let v3 = d_isMonoid_774 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe (coe du_setoid_202 (coe d_isMagma_496 (coe v4))))))
-- Algebra.Structures.IsSemiring._.sym
d_sym_1726 ::
  T_IsSemiring_1640 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1726 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0)))))))
-- Algebra.Structures.IsSemiring._.trans
d_trans_1728 ::
  T_IsSemiring_1640 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1728 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0)))))))
-- Algebra.Structures.IsSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_1730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsSemiring_1640 -> T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_1730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isSemiringWithoutOne_1730 v8
du_isSemiringWithoutOne_1730 ::
  T_IsSemiring_1640 -> T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_1730 v0
  = coe
      C_constructor_1430
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0)))
      (coe
         d_'42''45'cong_1558
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0)))
      (coe
         d_'42''45'assoc_1560
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0)))
      (coe
         d_distrib_1564
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v0)))
      (coe d_zero_1656 (coe v0))
-- Algebra.Structures.IsSemiring._.isNearSemiring
d_isNearSemiring_1734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> T_IsNearSemiring_1260
d_isNearSemiring_1734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isNearSemiring_1734 v8
du_isNearSemiring_1734 ::
  T_IsSemiring_1640 -> T_IsNearSemiring_1260
du_isNearSemiring_1734 v0
  = coe
      du_isNearSemiring_1428 (coe du_isSemiringWithoutOne_1730 (coe v0))
-- Algebra.Structures.IsSemiring._.zeroʳ
d_zero'691'_1736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> AgdaAny -> AgdaAny
d_zero'691'_1736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'691'_1736 v8
du_zero'691'_1736 :: T_IsSemiring_1640 -> AgdaAny -> AgdaAny
du_zero'691'_1736 v0
  = coe du_zero'691'_1426 (coe du_isSemiringWithoutOne_1730 (coe v0))
-- Algebra.Structures.IsSemiring._.zeroˡ
d_zero'737'_1738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1640 -> AgdaAny -> AgdaAny
d_zero'737'_1738 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'737'_1738 v8
du_zero'737'_1738 :: T_IsSemiring_1640 -> AgdaAny -> AgdaAny
du_zero'737'_1738 v0
  = coe du_zero'737'_1424 (coe du_isSemiringWithoutOne_1730 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring
d_IsCommutativeSemiring_1750 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsCommutativeSemiring_1750
  = C_constructor_1862 T_IsSemiring_1640
                       (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeSemiring.isSemiring
d_isSemiring_1764 ::
  T_IsCommutativeSemiring_1750 -> T_IsSemiring_1640
d_isSemiring_1764 v0
  = case coe v0 of
      C_constructor_1862 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemiring.*-comm
d_'42''45'comm_1766 ::
  T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_1766 v0
  = case coe v0 of
      C_constructor_1862 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemiring._.*-assoc
d_'42''45'assoc_1770 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1770 v0
  = coe
      d_'42''45'assoc_1560
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_1764 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiring._.*-cong
d_'42''45'cong_1772 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1772 v0
  = coe
      d_'42''45'cong_1558
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_1764 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiring._.∙-congʳ
d_'8729''45'cong'691'_1774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1774 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1774 v8
du_'8729''45'cong'691'_1774 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1774 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = coe du_'42''45'isMonoid_1618 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsCommutativeSemiring._.∙-congˡ
d_'8729''45'cong'737'_1776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1776 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1776 v8
du_'8729''45'cong'737'_1776 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1776 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = coe du_'42''45'isMonoid_1618 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsCommutativeSemiring._.*-identity
d_'42''45'identity_1778 ::
  T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1778 v0
  = coe
      d_'42''45'identity_1562
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_1764 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiring._.identityʳ
d_identity'691'_1780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
d_identity'691'_1780 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1780 v8
du_identity'691'_1780 ::
  T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
du_identity'691'_1780 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (coe du_identity'691'_754 (coe du_'42''45'isMonoid_1618 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiring._.identityˡ
d_identity'737'_1782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
d_identity'737'_1782 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1782 v8
du_identity'737'_1782 ::
  T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
du_identity'737'_1782 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (coe du_identity'737'_752 (coe du_'42''45'isMonoid_1618 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiring._.*-isMagma
d_'42''45'isMagma_1784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeSemiring_1750 -> T_IsMagma_178
d_'42''45'isMagma_1784 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_1784 v8
du_'42''45'isMagma_1784 ::
  T_IsCommutativeSemiring_1750 -> T_IsMagma_178
du_'42''45'isMagma_1784 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (coe
         du_'42''45'isMagma_1614
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.*-isMonoid
d_'42''45'isMonoid_1786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> T_IsMonoid_712
d_'42''45'isMonoid_1786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_1786 v8
du_'42''45'isMonoid_1786 ::
  T_IsCommutativeSemiring_1750 -> T_IsMonoid_712
du_'42''45'isMonoid_1786 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoid_1618
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.*-isSemigroup
d_'42''45'isSemigroup_1788 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> T_IsSemigroup_488
d_'42''45'isSemigroup_1788 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_1788 v8
du_'42''45'isSemigroup_1788 ::
  T_IsCommutativeSemiring_1750 -> T_IsSemigroup_488
du_'42''45'isSemigroup_1788 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (coe
         du_'42''45'isSemigroup_1616
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.assoc
d_assoc_1790 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1790 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774
            (coe
               d_'43''45'isCommutativeMonoid_1556
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1654
                  (coe d_isSemiring_1764 (coe v0))))))
-- Algebra.Structures.IsCommutativeSemiring._.comm
d_comm_1792 ::
  T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_1792 v0
  = coe
      d_comm_776
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe
            d_isSemiringWithoutAnnihilatingZero_1654
            (coe d_isSemiring_1764 (coe v0))))
-- Algebra.Structures.IsCommutativeSemiring._.∙-cong
d_'8729''45'cong_1794 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1794 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1556
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1654
                     (coe d_isSemiring_1764 (coe v0)))))))
-- Algebra.Structures.IsCommutativeSemiring._.∙-congʳ
d_'8729''45'cong'691'_1796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1796 v8
du_'8729''45'cong'691'_1796 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1796 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (let v4 = d_isMonoid_774 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (let v7 = coe du_setoid_202 (coe v6) in
                      coe
                        (let v8 = d_'8729''45'cong_188 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                    (coe v7)))))))))))
-- Algebra.Structures.IsCommutativeSemiring._.∙-congˡ
d_'8729''45'cong'737'_1798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1798 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1798 v8
du_'8729''45'cong'737'_1798 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1798 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (let v4 = d_isMonoid_774 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (let v7 = coe du_setoid_202 (coe v6) in
                      coe
                        (let v8 = d_'8729''45'cong_188 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                    (coe v7)))))))))))
-- Algebra.Structures.IsCommutativeSemiring._.identity
d_identity_1800 ::
  T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1800 v0
  = coe
      d_identity_724
      (coe
         d_isMonoid_774
         (coe
            d_'43''45'isCommutativeMonoid_1556
            (coe
               d_isSemiringWithoutAnnihilatingZero_1654
               (coe d_isSemiring_1764 (coe v0)))))
-- Algebra.Structures.IsCommutativeSemiring._.identityʳ
d_identity'691'_1802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
d_identity'691'_1802 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1802 v8
du_identity'691'_1802 ::
  T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
du_identity'691'_1802 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe (coe du_identity'691'_754 (coe d_isMonoid_774 (coe v3)))))
-- Algebra.Structures.IsCommutativeSemiring._.identityˡ
d_identity'737'_1804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
d_identity'737'_1804 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1804 v8
du_identity'737'_1804 ::
  T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
du_identity'737'_1804 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe (coe du_identity'737'_752 (coe d_isMonoid_774 (coe v3)))))
-- Algebra.Structures.IsCommutativeSemiring._.isCommutativeMagma
d_isCommutativeMagma_1806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_1806 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1806 v8
du_isCommutativeMagma_1806 ::
  T_IsCommutativeSemiring_1750 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_1806 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (coe
               du_isCommutativeMagma_606
               (coe du_isCommutativeSemigroup_814 (coe v3)))))
-- Algebra.Structures.IsCommutativeSemiring._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1808 ::
  T_IsCommutativeSemiring_1750 -> T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1808 v0
  = coe
      d_'43''45'isCommutativeMonoid_1556
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_1764 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiring._.isCommutativeSemigroup
d_isCommutativeSemigroup_1810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1810 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_1810 v8
du_isCommutativeSemigroup_1810 ::
  T_IsCommutativeSemiring_1750 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1810 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (coe
            du_isCommutativeSemigroup_814
            (coe d_'43''45'isCommutativeMonoid_1556 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiring._.isMagma
d_isMagma_1812 :: T_IsCommutativeSemiring_1750 -> T_IsMagma_178
d_isMagma_1812 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774
            (coe
               d_'43''45'isCommutativeMonoid_1556
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1654
                  (coe d_isSemiring_1764 (coe v0))))))
-- Algebra.Structures.IsCommutativeSemiring._.isMonoid
d_isMonoid_1814 :: T_IsCommutativeSemiring_1750 -> T_IsMonoid_712
d_isMonoid_1814 v0
  = coe
      d_isMonoid_774
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe
            d_isSemiringWithoutAnnihilatingZero_1654
            (coe d_isSemiring_1764 (coe v0))))
-- Algebra.Structures.IsCommutativeSemiring._.isSemigroup
d_isSemigroup_1816 ::
  T_IsCommutativeSemiring_1750 -> T_IsSemigroup_488
d_isSemigroup_1816 v0
  = coe
      d_isSemigroup_722
      (coe
         d_isMonoid_774
         (coe
            d_'43''45'isCommutativeMonoid_1556
            (coe
               d_isSemiringWithoutAnnihilatingZero_1654
               (coe d_isSemiring_1764 (coe v0)))))
-- Algebra.Structures.IsCommutativeSemiring._.isUnitalMagma
d_isUnitalMagma_1818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> T_IsUnitalMagma_666
d_isUnitalMagma_1818 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_1818 v8
du_isUnitalMagma_1818 ::
  T_IsCommutativeSemiring_1750 -> T_IsUnitalMagma_666
du_isUnitalMagma_1818 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe (coe du_isUnitalMagma_756 (coe d_isMonoid_774 (coe v3)))))
-- Algebra.Structures.IsCommutativeSemiring._.distrib
d_distrib_1820 ::
  T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1820 v0
  = coe
      d_distrib_1564
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_1764 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiring._.distribʳ
d_distrib'691'_1822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1822 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_1822 v8
du_distrib'691'_1822 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1822 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (coe
         du_distrib'691'_1568
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.distribˡ
d_distrib'737'_1824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_1824 v8
du_distrib'737'_1824 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1824 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (coe
         du_distrib'737'_1566
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.isEquivalence
d_isEquivalence_1826 ::
  T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1826 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1556
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1654
                     (coe d_isSemiring_1764 (coe v0)))))))
-- Algebra.Structures.IsCommutativeSemiring._.isNearSemiring
d_isNearSemiring_1828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> T_IsNearSemiring_1260
d_isNearSemiring_1828 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isNearSemiring_1828 v8
du_isNearSemiring_1828 ::
  T_IsCommutativeSemiring_1750 -> T_IsNearSemiring_1260
du_isNearSemiring_1828 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (coe
         du_isNearSemiring_1428 (coe du_isSemiringWithoutOne_1730 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.isPartialEquivalence
d_isPartialEquivalence_1830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1830 v8
du_isPartialEquivalence_1830 ::
  T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1830 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (let v4 = d_isMonoid_774 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                        (coe d_isEquivalence_186 (coe v6))))))))
-- Algebra.Structures.IsCommutativeSemiring._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1832 ::
  T_IsCommutativeSemiring_1750 ->
  T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_1832 v0
  = coe
      d_isSemiringWithoutAnnihilatingZero_1654
      (coe d_isSemiring_1764 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring._.isSemiringWithoutOne
d_isSemiringWithoutOne_1834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 -> T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_1834 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isSemiringWithoutOne_1834 v8
du_isSemiringWithoutOne_1834 ::
  T_IsCommutativeSemiring_1750 -> T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_1834 v0
  = coe du_isSemiringWithoutOne_1730 (coe d_isSemiring_1764 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring._.refl
d_refl_1836 :: T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
d_refl_1836 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe d_isSemiring_1764 (coe v0))))))))
-- Algebra.Structures.IsCommutativeSemiring._.reflexive
d_reflexive_1838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1838 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1838 v8
du_reflexive_1838 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1838 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (let v4 = d_isMonoid_774 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (\ v7 v8 v9 ->
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                          (coe d_isEquivalence_186 (coe v6)) v7))))))
-- Algebra.Structures.IsCommutativeSemiring._.setoid
d_setoid_1840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1840 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1840 v8
du_setoid_1840 ::
  T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1840 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (let v4 = d_isMonoid_774 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe (coe du_setoid_202 (coe d_isMagma_496 (coe v5)))))))
-- Algebra.Structures.IsCommutativeSemiring._.sym
d_sym_1842 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1842 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe d_isSemiring_1764 (coe v0))))))))
-- Algebra.Structures.IsCommutativeSemiring._.trans
d_trans_1844 ::
  T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1844 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe d_isSemiring_1764 (coe v0))))))))
-- Algebra.Structures.IsCommutativeSemiring._.zero
d_zero_1846 ::
  T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1846 v0 = coe d_zero_1656 (coe d_isSemiring_1764 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring._.zeroʳ
d_zero'691'_1848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
d_zero'691'_1848 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'691'_1848 v8
du_zero'691'_1848 ::
  T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
du_zero'691'_1848 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (coe du_zero'691'_1426 (coe du_isSemiringWithoutOne_1730 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.zeroˡ
d_zero'737'_1850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
d_zero'737'_1850 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'737'_1850 v8
du_zero'737'_1850 ::
  T_IsCommutativeSemiring_1750 -> AgdaAny -> AgdaAny
du_zero'737'_1850 v0
  = let v1 = d_isSemiring_1764 (coe v0) in
    coe
      (coe du_zero'737'_1424 (coe du_isSemiringWithoutOne_1730 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_1852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 ->
  T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_1852 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 v8
  = du_isCommutativeSemiringWithoutOne_1852 v8
du_isCommutativeSemiringWithoutOne_1852 ::
  T_IsCommutativeSemiring_1750 ->
  T_IsCommutativeSemiringWithoutOne_1438
du_isCommutativeSemiringWithoutOne_1852 v0
  = coe
      C_constructor_1526
      (coe du_isSemiringWithoutOne_1730 (coe d_isSemiring_1764 (coe v0)))
      (coe d_'42''45'comm_1766 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring._.isCommutativeMagma
d_isCommutativeMagma_1856 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1750 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_1856 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1856 v8
du_isCommutativeMagma_1856 ::
  T_IsCommutativeSemiring_1750 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_1856 v0
  = let v1 = coe du_isCommutativeSemiringWithoutOne_1852 (coe v0) in
    coe
      (coe
         du_isCommutativeMagma_606
         (coe du_'42''45'isCommutativeSemigroup_1520 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_1858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 -> T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_1858 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 v8
  = du_'42''45'isCommutativeSemigroup_1858 v8
du_'42''45'isCommutativeSemigroup_1858 ::
  T_IsCommutativeSemiring_1750 -> T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_1858 v0
  = coe
      du_'42''45'isCommutativeSemigroup_1520
      (coe du_isCommutativeSemiringWithoutOne_1852 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_1860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1750 -> T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_1860 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   v8
  = du_'42''45'isCommutativeMonoid_1860 v8
du_'42''45'isCommutativeMonoid_1860 ::
  T_IsCommutativeSemiring_1750 -> T_IsCommutativeMonoid_764
du_'42''45'isCommutativeMonoid_1860 v0
  = coe
      C_constructor_820
      (coe
         du_'42''45'isMonoid_1618
         (coe
            d_isSemiringWithoutAnnihilatingZero_1654
            (coe d_isSemiring_1764 (coe v0))))
      (coe d_'42''45'comm_1766 (coe v0))
-- Algebra.Structures.IsCancellativeCommutativeSemiring
d_IsCancellativeCommutativeSemiring_1872 a0 a1 a2 a3 a4 a5 a6 a7
  = ()
data T_IsCancellativeCommutativeSemiring_1872
  = C_constructor_1988 T_IsCommutativeSemiring_1750
                       (AgdaAny ->
                        AgdaAny ->
                        AgdaAny ->
                        (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
                        AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCancellativeCommutativeSemiring.isCommutativeSemiring
d_isCommutativeSemiring_1886 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_1886 v0
  = case coe v0 of
      C_constructor_1988 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCancellativeCommutativeSemiring.*-cancelˡ-nonZero
d_'42''45'cancel'737''45'nonZero_1888 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny
d_'42''45'cancel'737''45'nonZero_1888 v0
  = case coe v0 of
      C_constructor_1988 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-assoc
d_'42''45'assoc_1892 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1892 v0
  = coe
      d_'42''45'assoc_1560
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-comm
d_'42''45'comm_1894 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_1894 v0
  = coe
      d_'42''45'comm_1766 (coe d_isCommutativeSemiring_1886 (coe v0))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-cong
d_'42''45'cong_1896 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1896 v0
  = coe
      d_'42''45'cong_1558
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.∙-congʳ
d_'8729''45'cong'691'_1898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1898 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1898 v8
du_'8729''45'cong'691'_1898 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1898 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = coe du_'42''45'isMonoid_1618 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (let v7 = coe du_setoid_202 (coe v6) in
                      coe
                        (let v8 = d_'8729''45'cong_188 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                    (coe v7)))))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.∙-congˡ
d_'8729''45'cong'737'_1900 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1900 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1900 v8
du_'8729''45'cong'737'_1900 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1900 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = coe du_'42''45'isMonoid_1618 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (let v7 = coe du_setoid_202 (coe v6) in
                      coe
                        (let v8 = d_'8729''45'cong_188 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                    (coe v7)))))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-identity
d_'42''45'identity_1902 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1902 v0
  = coe
      d_'42''45'identity_1562
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.identityʳ
d_identity'691'_1904 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
d_identity'691'_1904 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1904 v8
du_identity'691'_1904 ::
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
du_identity'691'_1904 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (coe
               du_identity'691'_754 (coe du_'42''45'isMonoid_1618 (coe v3)))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.identityˡ
d_identity'737'_1906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
d_identity'737'_1906 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1906 v8
du_identity'737'_1906 ::
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
du_identity'737'_1906 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (coe
               du_identity'737'_752 (coe du_'42''45'isMonoid_1618 (coe v3)))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isCommutativeMagma
d_isCommutativeMagma_1908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeMagma_214
d_isCommutativeMagma_1908 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1908 v8
du_isCommutativeMagma_1908 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeMagma_214
du_isCommutativeMagma_1908 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = coe du_isCommutativeSemiringWithoutOne_1852 (coe v1) in
       coe
         (coe
            du_isCommutativeMagma_606
            (coe du_'42''45'isCommutativeSemigroup_1520 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_1910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_1910 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   v8
  = du_'42''45'isCommutativeMonoid_1910 v8
du_'42''45'isCommutativeMonoid_1910 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeMonoid_764
du_'42''45'isCommutativeMonoid_1910 v0
  = coe
      du_'42''45'isCommutativeMonoid_1860
      (coe d_isCommutativeSemiring_1886 (coe v0))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_1912 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_1912 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 v8
  = du_'42''45'isCommutativeSemigroup_1912 v8
du_'42''45'isCommutativeSemigroup_1912 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_1912 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (coe
         du_'42''45'isCommutativeSemigroup_1520
         (coe du_isCommutativeSemiringWithoutOne_1852 (coe v1)))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-isMagma
d_'42''45'isMagma_1914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsMagma_178
d_'42''45'isMagma_1914 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_1914 v8
du_'42''45'isMagma_1914 ::
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsMagma_178
du_'42''45'isMagma_1914 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (coe
            du_'42''45'isMagma_1614
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-isMonoid
d_'42''45'isMonoid_1916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsMonoid_712
d_'42''45'isMonoid_1916 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_1916 v8
du_'42''45'isMonoid_1916 ::
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsMonoid_712
du_'42''45'isMonoid_1916 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (coe
            du_'42''45'isMonoid_1618
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-isSemigroup
d_'42''45'isSemigroup_1918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsSemigroup_488
d_'42''45'isSemigroup_1918 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_1918 v8
du_'42''45'isSemigroup_1918 ::
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsSemigroup_488
du_'42''45'isSemigroup_1918 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (coe
            du_'42''45'isSemigroup_1616
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.assoc
d_assoc_1920 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1920 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774
            (coe
               d_'43''45'isCommutativeMonoid_1556
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1654
                  (coe
                     d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0)))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.comm
d_comm_1922 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_1922 v0
  = coe
      d_comm_776
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe
            d_isSemiringWithoutAnnihilatingZero_1654
            (coe
               d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0)))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.∙-cong
d_'8729''45'cong_1924 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1924 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1556
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1654
                     (coe
                        d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.∙-congʳ
d_'8729''45'cong'691'_1926 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1926 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1926 v8
du_'8729''45'cong'691'_1926 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1926 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (let v5 = d_isMonoid_774 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (let v8 = coe du_setoid_202 (coe v7) in
                         coe
                           (let v9 = d_'8729''45'cong_188 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                       (coe v8))))))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.∙-congˡ
d_'8729''45'cong'737'_1928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1928 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1928 v8
du_'8729''45'cong'737'_1928 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1928 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (let v5 = d_isMonoid_774 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (let v8 = coe du_setoid_202 (coe v7) in
                         coe
                           (let v9 = d_'8729''45'cong_188 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                       (coe v8))))))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.identity
d_identity_1930 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1930 v0
  = coe
      d_identity_724
      (coe
         d_isMonoid_774
         (coe
            d_'43''45'isCommutativeMonoid_1556
            (coe
               d_isSemiringWithoutAnnihilatingZero_1654
               (coe
                  d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.identityʳ
d_identity'691'_1932 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
d_identity'691'_1932 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1932 v8
du_identity'691'_1932 ::
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
du_identity'691'_1932 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe (coe du_identity'691'_754 (coe d_isMonoid_774 (coe v4))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.identityˡ
d_identity'737'_1934 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
d_identity'737'_1934 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1934 v8
du_identity'737'_1934 ::
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
du_identity'737'_1934 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe (coe du_identity'737'_752 (coe d_isMonoid_774 (coe v4))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isCommutativeMagma
d_isCommutativeMagma_1936 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeMagma_214
d_isCommutativeMagma_1936 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1936 v8
du_isCommutativeMagma_1936 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeMagma_214
du_isCommutativeMagma_1936 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (coe
                  du_isCommutativeMagma_606
                  (coe du_isCommutativeSemigroup_814 (coe v4))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1938 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1938 v0
  = coe
      d_'43''45'isCommutativeMonoid_1556
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isCommutativeSemigroup
d_isCommutativeSemigroup_1940 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_1940 v8
du_isCommutativeSemigroup_1940 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1940 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (coe
               du_isCommutativeSemigroup_814
               (coe d_'43''45'isCommutativeMonoid_1556 (coe v3)))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isMagma
d_isMagma_1942 ::
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsMagma_178
d_isMagma_1942 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774
            (coe
               d_'43''45'isCommutativeMonoid_1556
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1654
                  (coe
                     d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0)))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isMonoid
d_isMonoid_1944 ::
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsMonoid_712
d_isMonoid_1944 v0
  = coe
      d_isMonoid_774
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe
            d_isSemiringWithoutAnnihilatingZero_1654
            (coe
               d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0)))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isSemigroup
d_isSemigroup_1946 ::
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsSemigroup_488
d_isSemigroup_1946 v0
  = coe
      d_isSemigroup_722
      (coe
         d_isMonoid_774
         (coe
            d_'43''45'isCommutativeMonoid_1556
            (coe
               d_isSemiringWithoutAnnihilatingZero_1654
               (coe
                  d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isUnitalMagma
d_isUnitalMagma_1948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsUnitalMagma_666
d_isUnitalMagma_1948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_1948 v8
du_isUnitalMagma_1948 ::
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsUnitalMagma_666
du_isUnitalMagma_1948 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe (coe du_isUnitalMagma_756 (coe d_isMonoid_774 (coe v4))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.distrib
d_distrib_1950 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1950 v0
  = coe
      d_distrib_1564
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.distribʳ
d_distrib'691'_1952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1952 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_1952 v8
du_distrib'691'_1952 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1952 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (coe
            du_distrib'691'_1568
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.distribˡ
d_distrib'737'_1954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_1954 v8
du_distrib'737'_1954 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1954 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (coe
            du_distrib'737'_1566
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_1956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_1956 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 v8
  = du_isCommutativeSemiringWithoutOne_1956 v8
du_isCommutativeSemiringWithoutOne_1956 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsCommutativeSemiringWithoutOne_1438
du_isCommutativeSemiringWithoutOne_1956 v0
  = coe
      du_isCommutativeSemiringWithoutOne_1852
      (coe d_isCommutativeSemiring_1886 (coe v0))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isEquivalence
d_isEquivalence_1958 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1958 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1556
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1654
                     (coe
                        d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isNearSemiring
d_isNearSemiring_1960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsNearSemiring_1260
d_isNearSemiring_1960 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isNearSemiring_1960 v8
du_isNearSemiring_1960 ::
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsNearSemiring_1260
du_isNearSemiring_1960 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (coe
            du_isNearSemiring_1428
            (coe du_isSemiringWithoutOne_1730 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isPartialEquivalence
d_isPartialEquivalence_1962 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1962 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1962 v8
du_isPartialEquivalence_1962 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1962 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (let v5 = d_isMonoid_774 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                           (coe d_isEquivalence_186 (coe v7)))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isSemiring
d_isSemiring_1964 ::
  T_IsCancellativeCommutativeSemiring_1872 -> T_IsSemiring_1640
d_isSemiring_1964 v0
  = coe d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1966 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_1966 v0
  = coe
      d_isSemiringWithoutAnnihilatingZero_1654
      (coe d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0)))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isSemiringWithoutOne
d_isSemiringWithoutOne_1968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_1968 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isSemiringWithoutOne_1968 v8
du_isSemiringWithoutOne_1968 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_1968 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (coe du_isSemiringWithoutOne_1730 (coe d_isSemiring_1764 (coe v1)))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.refl
d_refl_1970 ::
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
d_refl_1970 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe
                           d_isSemiring_1764
                           (coe d_isCommutativeSemiring_1886 (coe v0)))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.reflexive
d_reflexive_1972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1972 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1972 v8
du_reflexive_1972 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1972 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (let v5 = d_isMonoid_774 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (\ v8 v9 v10 ->
                           coe
                             MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                             (coe d_isEquivalence_186 (coe v7)) v8)))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.setoid
d_setoid_1974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1974 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1974 v8
du_setoid_1974 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1974 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (let v5 = d_isMonoid_774 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe (coe du_setoid_202 (coe d_isMagma_496 (coe v6))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.sym
d_sym_1976 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1976 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe
                           d_isSemiring_1764
                           (coe d_isCommutativeSemiring_1886 (coe v0)))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.trans
d_trans_1978 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1978 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe
                           d_isSemiring_1764
                           (coe d_isCommutativeSemiring_1886 (coe v0)))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.zero
d_zero_1980 ::
  T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1980 v0
  = coe
      d_zero_1656
      (coe d_isSemiring_1764 (coe d_isCommutativeSemiring_1886 (coe v0)))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.zeroʳ
d_zero'691'_1982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
d_zero'691'_1982 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'691'_1982 v8
du_zero'691'_1982 ::
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
du_zero'691'_1982 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (coe
            du_zero'691'_1426 (coe du_isSemiringWithoutOne_1730 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.zeroˡ
d_zero'737'_1984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
d_zero'737'_1984 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'737'_1984 v8
du_zero'737'_1984 ::
  T_IsCancellativeCommutativeSemiring_1872 -> AgdaAny -> AgdaAny
du_zero'737'_1984 v0
  = let v1 = d_isCommutativeSemiring_1886 (coe v0) in
    coe
      (let v2 = d_isSemiring_1764 (coe v1) in
       coe
         (coe
            du_zero'737'_1424 (coe du_isSemiringWithoutOne_1730 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring.*-cancelʳ-nonZero
d_'42''45'cancel'691''45'nonZero_1986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny
d_'42''45'cancel'691''45'nonZero_1986 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
                                      ~v7 v8
  = du_'42''45'cancel'691''45'nonZero_1986 v5 v8
du_'42''45'cancel'691''45'nonZero_1986 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCancellativeCommutativeSemiring_1872 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny
du_'42''45'cancel'691''45'nonZero_1986 v0 v1
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'almostCancel'737''8658'almostCancel'691'_400
      (coe
         du_setoid_202
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe
                           d_isSemiring_1764
                           (coe d_isCommutativeSemiring_1886 (coe v1)))))))))
      (coe v0)
      (coe
         d_'42''45'comm_1766 (coe d_isCommutativeSemiring_1886 (coe v1)))
      (coe d_'42''45'cancel'737''45'nonZero_1888 (coe v1))
-- Algebra.Structures.IsIdempotentSemiring
d_IsIdempotentSemiring_1998 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsIdempotentSemiring_1998
  = C_constructor_2110 T_IsSemiring_1640 (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsIdempotentSemiring.isSemiring
d_isSemiring_2012 ::
  T_IsIdempotentSemiring_1998 -> T_IsSemiring_1640
d_isSemiring_2012 v0
  = case coe v0 of
      C_constructor_2110 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentSemiring.+-idem
d_'43''45'idem_2014 ::
  T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
d_'43''45'idem_2014 v0
  = case coe v0 of
      C_constructor_2110 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentSemiring._.*-assoc
d_'42''45'assoc_2018 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2018 v0
  = coe
      d_'42''45'assoc_1560
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_2012 (coe v0)))
-- Algebra.Structures.IsIdempotentSemiring._.*-cong
d_'42''45'cong_2020 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2020 v0
  = coe
      d_'42''45'cong_1558
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_2012 (coe v0)))
-- Algebra.Structures.IsIdempotentSemiring._.∙-congʳ
d_'8729''45'cong'691'_2022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2022 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_2022 v8
du_'8729''45'cong'691'_2022 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2022 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = coe du_'42''45'isMonoid_1618 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsIdempotentSemiring._.∙-congˡ
d_'8729''45'cong'737'_2024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2024 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_2024 v8
du_'8729''45'cong'737'_2024 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2024 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = coe du_'42''45'isMonoid_1618 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsIdempotentSemiring._.*-identity
d_'42''45'identity_2026 ::
  T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2026 v0
  = coe
      d_'42''45'identity_1562
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_2012 (coe v0)))
-- Algebra.Structures.IsIdempotentSemiring._.identityʳ
d_identity'691'_2028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
d_identity'691'_2028 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_2028 v8
du_identity'691'_2028 ::
  T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
du_identity'691'_2028 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (coe du_identity'691'_754 (coe du_'42''45'isMonoid_1618 (coe v2))))
-- Algebra.Structures.IsIdempotentSemiring._.identityˡ
d_identity'737'_2030 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
d_identity'737'_2030 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_2030 v8
du_identity'737'_2030 ::
  T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
du_identity'737'_2030 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (coe du_identity'737'_752 (coe du_'42''45'isMonoid_1618 (coe v2))))
-- Algebra.Structures.IsIdempotentSemiring._.*-isMagma
d_'42''45'isMagma_2032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsIdempotentSemiring_1998 -> T_IsMagma_178
d_'42''45'isMagma_2032 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_2032 v8
du_'42''45'isMagma_2032 ::
  T_IsIdempotentSemiring_1998 -> T_IsMagma_178
du_'42''45'isMagma_2032 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (coe
         du_'42''45'isMagma_1614
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.*-isMonoid
d_'42''45'isMonoid_2034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsIdempotentSemiring_1998 -> T_IsMonoid_712
d_'42''45'isMonoid_2034 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_2034 v8
du_'42''45'isMonoid_2034 ::
  T_IsIdempotentSemiring_1998 -> T_IsMonoid_712
du_'42''45'isMonoid_2034 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoid_1618
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.*-isSemigroup
d_'42''45'isSemigroup_2036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> T_IsSemigroup_488
d_'42''45'isSemigroup_2036 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_2036 v8
du_'42''45'isSemigroup_2036 ::
  T_IsIdempotentSemiring_1998 -> T_IsSemigroup_488
du_'42''45'isSemigroup_2036 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (coe
         du_'42''45'isSemigroup_1616
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.assoc
d_assoc_2038 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2038 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774
            (coe
               d_'43''45'isCommutativeMonoid_1556
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1654
                  (coe d_isSemiring_2012 (coe v0))))))
-- Algebra.Structures.IsIdempotentSemiring._.comm
d_comm_2040 ::
  T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2040 v0
  = coe
      d_comm_776
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe
            d_isSemiringWithoutAnnihilatingZero_1654
            (coe d_isSemiring_2012 (coe v0))))
-- Algebra.Structures.IsIdempotentSemiring._.∙-cong
d_'8729''45'cong_2042 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2042 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1556
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1654
                     (coe d_isSemiring_2012 (coe v0)))))))
-- Algebra.Structures.IsIdempotentSemiring._.∙-congʳ
d_'8729''45'cong'691'_2044 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2044 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_2044 v8
du_'8729''45'cong'691'_2044 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2044 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (let v4 = d_isMonoid_774 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (let v7 = coe du_setoid_202 (coe v6) in
                      coe
                        (let v8 = d_'8729''45'cong_188 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                    (coe v7)))))))))))
-- Algebra.Structures.IsIdempotentSemiring._.∙-congˡ
d_'8729''45'cong'737'_2046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2046 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_2046 v8
du_'8729''45'cong'737'_2046 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2046 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (let v4 = d_isMonoid_774 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (let v7 = coe du_setoid_202 (coe v6) in
                      coe
                        (let v8 = d_'8729''45'cong_188 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                    (coe v7)))))))))))
-- Algebra.Structures.IsIdempotentSemiring._.identity
d_identity_2048 ::
  T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2048 v0
  = coe
      d_identity_724
      (coe
         d_isMonoid_774
         (coe
            d_'43''45'isCommutativeMonoid_1556
            (coe
               d_isSemiringWithoutAnnihilatingZero_1654
               (coe d_isSemiring_2012 (coe v0)))))
-- Algebra.Structures.IsIdempotentSemiring._.identityʳ
d_identity'691'_2050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
d_identity'691'_2050 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_2050 v8
du_identity'691'_2050 ::
  T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
du_identity'691'_2050 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe (coe du_identity'691'_754 (coe d_isMonoid_774 (coe v3)))))
-- Algebra.Structures.IsIdempotentSemiring._.identityˡ
d_identity'737'_2052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
d_identity'737'_2052 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_2052 v8
du_identity'737'_2052 ::
  T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
du_identity'737'_2052 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe (coe du_identity'737'_752 (coe d_isMonoid_774 (coe v3)))))
-- Algebra.Structures.IsIdempotentSemiring._.isCommutativeMagma
d_isCommutativeMagma_2054 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_2054 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_2054 v8
du_isCommutativeMagma_2054 ::
  T_IsIdempotentSemiring_1998 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_2054 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (coe
               du_isCommutativeMagma_606
               (coe du_isCommutativeSemigroup_814 (coe v3)))))
-- Algebra.Structures.IsIdempotentSemiring._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2056 ::
  T_IsIdempotentSemiring_1998 -> T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2056 v0
  = coe
      d_'43''45'isCommutativeMonoid_1556
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_2012 (coe v0)))
-- Algebra.Structures.IsIdempotentSemiring._.isCommutativeSemigroup
d_isCommutativeSemigroup_2058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2058 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_2058 v8
du_isCommutativeSemigroup_2058 ::
  T_IsIdempotentSemiring_1998 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2058 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (coe
            du_isCommutativeSemigroup_814
            (coe d_'43''45'isCommutativeMonoid_1556 (coe v2))))
-- Algebra.Structures.IsIdempotentSemiring._.isMagma
d_isMagma_2060 :: T_IsIdempotentSemiring_1998 -> T_IsMagma_178
d_isMagma_2060 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774
            (coe
               d_'43''45'isCommutativeMonoid_1556
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1654
                  (coe d_isSemiring_2012 (coe v0))))))
-- Algebra.Structures.IsIdempotentSemiring._.isMonoid
d_isMonoid_2062 :: T_IsIdempotentSemiring_1998 -> T_IsMonoid_712
d_isMonoid_2062 v0
  = coe
      d_isMonoid_774
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe
            d_isSemiringWithoutAnnihilatingZero_1654
            (coe d_isSemiring_2012 (coe v0))))
-- Algebra.Structures.IsIdempotentSemiring._.isSemigroup
d_isSemigroup_2064 ::
  T_IsIdempotentSemiring_1998 -> T_IsSemigroup_488
d_isSemigroup_2064 v0
  = coe
      d_isSemigroup_722
      (coe
         d_isMonoid_774
         (coe
            d_'43''45'isCommutativeMonoid_1556
            (coe
               d_isSemiringWithoutAnnihilatingZero_1654
               (coe d_isSemiring_2012 (coe v0)))))
-- Algebra.Structures.IsIdempotentSemiring._.isUnitalMagma
d_isUnitalMagma_2066 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> T_IsUnitalMagma_666
d_isUnitalMagma_2066 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_2066 v8
du_isUnitalMagma_2066 ::
  T_IsIdempotentSemiring_1998 -> T_IsUnitalMagma_666
du_isUnitalMagma_2066 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe (coe du_isUnitalMagma_756 (coe d_isMonoid_774 (coe v3)))))
-- Algebra.Structures.IsIdempotentSemiring._.distrib
d_distrib_2068 ::
  T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2068 v0
  = coe
      d_distrib_1564
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_2012 (coe v0)))
-- Algebra.Structures.IsIdempotentSemiring._.distribʳ
d_distrib'691'_2070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2070 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_2070 v8
du_distrib'691'_2070 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2070 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (coe
         du_distrib'691'_1568
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.distribˡ
d_distrib'737'_2072 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2072 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_2072 v8
du_distrib'737'_2072 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2072 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (coe
         du_distrib'737'_1566
         (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.isEquivalence
d_isEquivalence_2074 ::
  T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2074 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1556
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1654
                     (coe d_isSemiring_2012 (coe v0)))))))
-- Algebra.Structures.IsIdempotentSemiring._.isNearSemiring
d_isNearSemiring_2076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> T_IsNearSemiring_1260
d_isNearSemiring_2076 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isNearSemiring_2076 v8
du_isNearSemiring_2076 ::
  T_IsIdempotentSemiring_1998 -> T_IsNearSemiring_1260
du_isNearSemiring_2076 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (coe
         du_isNearSemiring_1428 (coe du_isSemiringWithoutOne_1730 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.isPartialEquivalence
d_isPartialEquivalence_2078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2078 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_2078 v8
du_isPartialEquivalence_2078 ::
  T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2078 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (let v4 = d_isMonoid_774 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                        (coe d_isEquivalence_186 (coe v6))))))))
-- Algebra.Structures.IsIdempotentSemiring._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2080 ::
  T_IsIdempotentSemiring_1998 ->
  T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2080 v0
  = coe
      d_isSemiringWithoutAnnihilatingZero_1654
      (coe d_isSemiring_2012 (coe v0))
-- Algebra.Structures.IsIdempotentSemiring._.isSemiringWithoutOne
d_isSemiringWithoutOne_2082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 -> T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2082 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isSemiringWithoutOne_2082 v8
du_isSemiringWithoutOne_2082 ::
  T_IsIdempotentSemiring_1998 -> T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_2082 v0
  = coe du_isSemiringWithoutOne_1730 (coe d_isSemiring_2012 (coe v0))
-- Algebra.Structures.IsIdempotentSemiring._.refl
d_refl_2084 :: T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
d_refl_2084 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe d_isSemiring_2012 (coe v0))))))))
-- Algebra.Structures.IsIdempotentSemiring._.reflexive
d_reflexive_2086 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2086 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_2086 v8
du_reflexive_2086 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2086 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (let v4 = d_isMonoid_774 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (\ v7 v8 v9 ->
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                          (coe d_isEquivalence_186 (coe v6)) v7))))))
-- Algebra.Structures.IsIdempotentSemiring._.setoid
d_setoid_2088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2088 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_2088 v8
du_setoid_2088 ::
  T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2088 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1556 (coe v2) in
          coe
            (let v4 = d_isMonoid_774 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe (coe du_setoid_202 (coe d_isMagma_496 (coe v5)))))))
-- Algebra.Structures.IsIdempotentSemiring._.sym
d_sym_2090 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2090 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe d_isSemiring_2012 (coe v0))))))))
-- Algebra.Structures.IsIdempotentSemiring._.trans
d_trans_2092 ::
  T_IsIdempotentSemiring_1998 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2092 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe d_isSemiring_2012 (coe v0))))))))
-- Algebra.Structures.IsIdempotentSemiring._.zero
d_zero_2094 ::
  T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2094 v0 = coe d_zero_1656 (coe d_isSemiring_2012 (coe v0))
-- Algebra.Structures.IsIdempotentSemiring._.zeroʳ
d_zero'691'_2096 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
d_zero'691'_2096 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'691'_2096 v8
du_zero'691'_2096 ::
  T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
du_zero'691'_2096 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (coe du_zero'691'_1426 (coe du_isSemiringWithoutOne_1730 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.zeroˡ
d_zero'737'_2098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
d_zero'737'_2098 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'737'_2098 v8
du_zero'737'_2098 ::
  T_IsIdempotentSemiring_1998 -> AgdaAny -> AgdaAny
du_zero'737'_2098 v0
  = let v1 = d_isSemiring_2012 (coe v0) in
    coe
      (coe du_zero'737'_1424 (coe du_isSemiringWithoutOne_1730 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_2100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1998 -> T_IsIdempotentCommutativeMonoid_884
d_'43''45'isIdempotentCommutativeMonoid_2100 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 ~v7 v8
  = du_'43''45'isIdempotentCommutativeMonoid_2100 v8
du_'43''45'isIdempotentCommutativeMonoid_2100 ::
  T_IsIdempotentSemiring_1998 -> T_IsIdempotentCommutativeMonoid_884
du_'43''45'isIdempotentCommutativeMonoid_2100 v0
  = coe
      C_constructor_950
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe
            d_isSemiringWithoutAnnihilatingZero_1654
            (coe d_isSemiring_2012 (coe v0))))
      (coe d_'43''45'idem_2014 (coe v0))
-- Algebra.Structures.IsIdempotentSemiring._.isBand
d_isBand_2104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsIdempotentSemiring_1998 -> T_IsBand_526
d_isBand_2104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isBand_2104 v8
du_isBand_2104 :: T_IsIdempotentSemiring_1998 -> T_IsBand_526
du_isBand_2104 v0
  = let v1
          = coe du_'43''45'isIdempotentCommutativeMonoid_2100 (coe v0) in
    coe (coe du_isBand_876 (coe du_isIdempotentMonoid_942 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.isCommutativeBand
d_isCommutativeBand_2106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> T_IsCommutativeBand_612
d_isCommutativeBand_2106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeBand_2106 v8
du_isCommutativeBand_2106 ::
  T_IsIdempotentSemiring_1998 -> T_IsCommutativeBand_612
du_isCommutativeBand_2106 v0
  = coe
      du_isCommutativeBand_948
      (coe du_'43''45'isIdempotentCommutativeMonoid_2100 (coe v0))
-- Algebra.Structures.IsIdempotentSemiring._.isIdempotentMonoid
d_isIdempotentMonoid_2108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1998 -> T_IsIdempotentMonoid_826
d_isIdempotentMonoid_2108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isIdempotentMonoid_2108 v8
du_isIdempotentMonoid_2108 ::
  T_IsIdempotentSemiring_1998 -> T_IsIdempotentMonoid_826
du_isIdempotentMonoid_2108 v0
  = coe
      du_isIdempotentMonoid_942
      (coe du_'43''45'isIdempotentCommutativeMonoid_2100 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra
d_IsKleeneAlgebra_2122 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsKleeneAlgebra_2122
  = C_constructor_2250 T_IsIdempotentSemiring_1998
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsKleeneAlgebra.isIdempotentSemiring
d_isIdempotentSemiring_2140 ::
  T_IsKleeneAlgebra_2122 -> T_IsIdempotentSemiring_1998
d_isIdempotentSemiring_2140 v0
  = case coe v0 of
      C_constructor_2250 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsKleeneAlgebra.starExpansive
d_starExpansive_2142 ::
  T_IsKleeneAlgebra_2122 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starExpansive_2142 v0
  = case coe v0 of
      C_constructor_2250 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsKleeneAlgebra.starDestructive
d_starDestructive_2144 ::
  T_IsKleeneAlgebra_2122 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starDestructive_2144 v0
  = case coe v0 of
      C_constructor_2250 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsKleeneAlgebra._.*-assoc
d_'42''45'assoc_2148 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2148 v0
  = coe
      d_'42''45'assoc_1560
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0))))
-- Algebra.Structures.IsKleeneAlgebra._.*-cong
d_'42''45'cong_2150 ::
  T_IsKleeneAlgebra_2122 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2150 v0
  = coe
      d_'42''45'cong_1558
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0))))
-- Algebra.Structures.IsKleeneAlgebra._.∙-congʳ
d_'8729''45'cong'691'_2152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2152 v9
du_'8729''45'cong'691'_2152 ::
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2152 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = coe du_'42''45'isMonoid_1618 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (let v7 = coe du_setoid_202 (coe v6) in
                      coe
                        (let v8 = d_'8729''45'cong_188 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                    (coe v7)))))))))))
-- Algebra.Structures.IsKleeneAlgebra._.∙-congˡ
d_'8729''45'cong'737'_2154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2154 v9
du_'8729''45'cong'737'_2154 ::
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2154 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = coe du_'42''45'isMonoid_1618 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (let v7 = coe du_setoid_202 (coe v6) in
                      coe
                        (let v8 = d_'8729''45'cong_188 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                    (coe v7)))))))))))
-- Algebra.Structures.IsKleeneAlgebra._.*-identity
d_'42''45'identity_2156 ::
  T_IsKleeneAlgebra_2122 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2156 v0
  = coe
      d_'42''45'identity_1562
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0))))
-- Algebra.Structures.IsKleeneAlgebra._.identityʳ
d_identity'691'_2158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
d_identity'691'_2158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2158 v9
du_identity'691'_2158 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
du_identity'691'_2158 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (coe
               du_identity'691'_754 (coe du_'42''45'isMonoid_1618 (coe v3)))))
-- Algebra.Structures.IsKleeneAlgebra._.identityˡ
d_identity'737'_2160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
d_identity'737'_2160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2160 v9
du_identity'737'_2160 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
du_identity'737'_2160 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (coe
               du_identity'737'_752 (coe du_'42''45'isMonoid_1618 (coe v3)))))
-- Algebra.Structures.IsKleeneAlgebra._.*-isMagma
d_'42''45'isMagma_2162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> T_IsMagma_178
d_'42''45'isMagma_2162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMagma_2162 v9
du_'42''45'isMagma_2162 :: T_IsKleeneAlgebra_2122 -> T_IsMagma_178
du_'42''45'isMagma_2162 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (coe
            du_'42''45'isMagma_1614
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.*-isMonoid
d_'42''45'isMonoid_2164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> T_IsMonoid_712
d_'42''45'isMonoid_2164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMonoid_2164 v9
du_'42''45'isMonoid_2164 ::
  T_IsKleeneAlgebra_2122 -> T_IsMonoid_712
du_'42''45'isMonoid_2164 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (coe
            du_'42''45'isMonoid_1618
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.*-isSemigroup
d_'42''45'isSemigroup_2166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> T_IsSemigroup_488
d_'42''45'isSemigroup_2166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isSemigroup_2166 v9
du_'42''45'isSemigroup_2166 ::
  T_IsKleeneAlgebra_2122 -> T_IsSemigroup_488
du_'42''45'isSemigroup_2166 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (coe
            du_'42''45'isSemigroup_1616
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.assoc
d_assoc_2168 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2168 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774
            (coe
               d_'43''45'isCommutativeMonoid_1556
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1654
                  (coe
                     d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0)))))))
-- Algebra.Structures.IsKleeneAlgebra._.comm
d_comm_2170 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2170 v0
  = coe
      d_comm_776
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe
            d_isSemiringWithoutAnnihilatingZero_1654
            (coe
               d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0)))))
-- Algebra.Structures.IsKleeneAlgebra._.∙-cong
d_'8729''45'cong_2172 ::
  T_IsKleeneAlgebra_2122 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2172 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1556
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1654
                     (coe
                        d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0))))))))
-- Algebra.Structures.IsKleeneAlgebra._.∙-congʳ
d_'8729''45'cong'691'_2174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2174 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2174 v9
du_'8729''45'cong'691'_2174 ::
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2174 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (let v5 = d_isMonoid_774 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (let v8 = coe du_setoid_202 (coe v7) in
                         coe
                           (let v9 = d_'8729''45'cong_188 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                       (coe v8))))))))))))
-- Algebra.Structures.IsKleeneAlgebra._.∙-congˡ
d_'8729''45'cong'737'_2176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2176 v9
du_'8729''45'cong'737'_2176 ::
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2176 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (let v5 = d_isMonoid_774 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (let v8 = coe du_setoid_202 (coe v7) in
                         coe
                           (let v9 = d_'8729''45'cong_188 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                       (coe v8))))))))))))
-- Algebra.Structures.IsKleeneAlgebra._.+-idem
d_'43''45'idem_2178 :: T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
d_'43''45'idem_2178 v0
  = coe
      d_'43''45'idem_2014 (coe d_isIdempotentSemiring_2140 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra._.identity
d_identity_2180 ::
  T_IsKleeneAlgebra_2122 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2180 v0
  = coe
      d_identity_724
      (coe
         d_isMonoid_774
         (coe
            d_'43''45'isCommutativeMonoid_1556
            (coe
               d_isSemiringWithoutAnnihilatingZero_1654
               (coe
                  d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0))))))
-- Algebra.Structures.IsKleeneAlgebra._.identityʳ
d_identity'691'_2182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
d_identity'691'_2182 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2182 v9
du_identity'691'_2182 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
du_identity'691'_2182 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe (coe du_identity'691'_754 (coe d_isMonoid_774 (coe v4))))))
-- Algebra.Structures.IsKleeneAlgebra._.identityˡ
d_identity'737'_2184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
d_identity'737'_2184 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2184 v9
du_identity'737'_2184 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
du_identity'737'_2184 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe (coe du_identity'737'_752 (coe d_isMonoid_774 (coe v4))))))
-- Algebra.Structures.IsKleeneAlgebra._.isBand
d_isBand_2186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> T_IsBand_526
d_isBand_2186 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isBand_2186 v9
du_isBand_2186 :: T_IsKleeneAlgebra_2122 -> T_IsBand_526
du_isBand_2186 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2
             = coe du_'43''45'isIdempotentCommutativeMonoid_2100 (coe v1) in
       coe (coe du_isBand_876 (coe du_isIdempotentMonoid_942 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.isCommutativeBand
d_isCommutativeBand_2188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2122 -> T_IsCommutativeBand_612
d_isCommutativeBand_2188 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeBand_2188 v9
du_isCommutativeBand_2188 ::
  T_IsKleeneAlgebra_2122 -> T_IsCommutativeBand_612
du_isCommutativeBand_2188 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (coe
         du_isCommutativeBand_948
         (coe du_'43''45'isIdempotentCommutativeMonoid_2100 (coe v1)))
-- Algebra.Structures.IsKleeneAlgebra._.isCommutativeMagma
d_isCommutativeMagma_2190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2122 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_2190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_2190 v9
du_isCommutativeMagma_2190 ::
  T_IsKleeneAlgebra_2122 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_2190 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (coe
                  du_isCommutativeMagma_606
                  (coe du_isCommutativeSemigroup_814 (coe v4))))))
-- Algebra.Structures.IsKleeneAlgebra._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2192 ::
  T_IsKleeneAlgebra_2122 -> T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2192 v0
  = coe
      d_'43''45'isCommutativeMonoid_1556
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0))))
-- Algebra.Structures.IsKleeneAlgebra._.isCommutativeSemigroup
d_isCommutativeSemigroup_2194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2122 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              v9
  = du_isCommutativeSemigroup_2194 v9
du_isCommutativeSemigroup_2194 ::
  T_IsKleeneAlgebra_2122 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2194 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (coe
               du_isCommutativeSemigroup_814
               (coe d_'43''45'isCommutativeMonoid_1556 (coe v3)))))
-- Algebra.Structures.IsKleeneAlgebra._.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_2196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 -> T_IsIdempotentCommutativeMonoid_884
d_'43''45'isIdempotentCommutativeMonoid_2196 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 ~v7 ~v8 v9
  = du_'43''45'isIdempotentCommutativeMonoid_2196 v9
du_'43''45'isIdempotentCommutativeMonoid_2196 ::
  T_IsKleeneAlgebra_2122 -> T_IsIdempotentCommutativeMonoid_884
du_'43''45'isIdempotentCommutativeMonoid_2196 v0
  = coe
      du_'43''45'isIdempotentCommutativeMonoid_2100
      (coe d_isIdempotentSemiring_2140 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra._.isIdempotentMonoid
d_isIdempotentMonoid_2198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2122 -> T_IsIdempotentMonoid_826
d_isIdempotentMonoid_2198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isIdempotentMonoid_2198 v9
du_isIdempotentMonoid_2198 ::
  T_IsKleeneAlgebra_2122 -> T_IsIdempotentMonoid_826
du_isIdempotentMonoid_2198 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (coe
         du_isIdempotentMonoid_942
         (coe du_'43''45'isIdempotentCommutativeMonoid_2100 (coe v1)))
-- Algebra.Structures.IsKleeneAlgebra._.isMagma
d_isMagma_2200 :: T_IsKleeneAlgebra_2122 -> T_IsMagma_178
d_isMagma_2200 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_774
            (coe
               d_'43''45'isCommutativeMonoid_1556
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1654
                  (coe
                     d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0)))))))
-- Algebra.Structures.IsKleeneAlgebra._.isMonoid
d_isMonoid_2202 :: T_IsKleeneAlgebra_2122 -> T_IsMonoid_712
d_isMonoid_2202 v0
  = coe
      d_isMonoid_774
      (coe
         d_'43''45'isCommutativeMonoid_1556
         (coe
            d_isSemiringWithoutAnnihilatingZero_1654
            (coe
               d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0)))))
-- Algebra.Structures.IsKleeneAlgebra._.isSemigroup
d_isSemigroup_2204 :: T_IsKleeneAlgebra_2122 -> T_IsSemigroup_488
d_isSemigroup_2204 v0
  = coe
      d_isSemigroup_722
      (coe
         d_isMonoid_774
         (coe
            d_'43''45'isCommutativeMonoid_1556
            (coe
               d_isSemiringWithoutAnnihilatingZero_1654
               (coe
                  d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0))))))
-- Algebra.Structures.IsKleeneAlgebra._.isUnitalMagma
d_isUnitalMagma_2206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> T_IsUnitalMagma_666
d_isUnitalMagma_2206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_2206 v9
du_isUnitalMagma_2206 ::
  T_IsKleeneAlgebra_2122 -> T_IsUnitalMagma_666
du_isUnitalMagma_2206 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe (coe du_isUnitalMagma_756 (coe d_isMonoid_774 (coe v4))))))
-- Algebra.Structures.IsKleeneAlgebra._.distrib
d_distrib_2208 ::
  T_IsKleeneAlgebra_2122 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2208 v0
  = coe
      d_distrib_1564
      (coe
         d_isSemiringWithoutAnnihilatingZero_1654
         (coe d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0))))
-- Algebra.Structures.IsKleeneAlgebra._.distribʳ
d_distrib'691'_2210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'691'_2210 v9
du_distrib'691'_2210 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2210 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (coe
            du_distrib'691'_1568
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.distribˡ
d_distrib'737'_2212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'737'_2212 v9
du_distrib'737'_2212 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2212 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (coe
            du_distrib'737'_1566
            (coe d_isSemiringWithoutAnnihilatingZero_1654 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.isEquivalence
d_isEquivalence_2214 ::
  T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2214 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_774
               (coe
                  d_'43''45'isCommutativeMonoid_1556
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1654
                     (coe
                        d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0))))))))
-- Algebra.Structures.IsKleeneAlgebra._.isNearSemiring
d_isNearSemiring_2216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2122 -> T_IsNearSemiring_1260
d_isNearSemiring_2216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isNearSemiring_2216 v9
du_isNearSemiring_2216 ::
  T_IsKleeneAlgebra_2122 -> T_IsNearSemiring_1260
du_isNearSemiring_2216 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (coe
            du_isNearSemiring_1428
            (coe du_isSemiringWithoutOne_1730 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.isPartialEquivalence
d_isPartialEquivalence_2218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_2218 v9
du_isPartialEquivalence_2218 ::
  T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2218 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (let v5 = d_isMonoid_774 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                           (coe d_isEquivalence_186 (coe v7)))))))))
-- Algebra.Structures.IsKleeneAlgebra._.isSemiring
d_isSemiring_2220 :: T_IsKleeneAlgebra_2122 -> T_IsSemiring_1640
d_isSemiring_2220 v0
  = coe d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2222 ::
  T_IsKleeneAlgebra_2122 -> T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2222 v0
  = coe
      d_isSemiringWithoutAnnihilatingZero_1654
      (coe d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0)))
-- Algebra.Structures.IsKleeneAlgebra._.isSemiringWithoutOne
d_isSemiringWithoutOne_2224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2122 -> T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isSemiringWithoutOne_2224 v9
du_isSemiringWithoutOne_2224 ::
  T_IsKleeneAlgebra_2122 -> T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_2224 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (coe du_isSemiringWithoutOne_1730 (coe d_isSemiring_2012 (coe v1)))
-- Algebra.Structures.IsKleeneAlgebra._.refl
d_refl_2226 :: T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
d_refl_2226 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe
                           d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0)))))))))
-- Algebra.Structures.IsKleeneAlgebra._.reflexive
d_reflexive_2228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_2228 v9
du_reflexive_2228 ::
  T_IsKleeneAlgebra_2122 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2228 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (let v5 = d_isMonoid_774 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (\ v8 v9 v10 ->
                           coe
                             MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                             (coe d_isEquivalence_186 (coe v7)) v8)))))))
-- Algebra.Structures.IsKleeneAlgebra._.setoid
d_setoid_2230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_2230 v9
du_setoid_2230 ::
  T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2230 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1654 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1556 (coe v3) in
             coe
               (let v5 = d_isMonoid_774 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe (coe du_setoid_202 (coe d_isMagma_496 (coe v6))))))))
-- Algebra.Structures.IsKleeneAlgebra._.sym
d_sym_2232 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe
                           d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0)))))))))
-- Algebra.Structures.IsKleeneAlgebra._.trans
d_trans_2234 ::
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2234 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_774
                  (coe
                     d_'43''45'isCommutativeMonoid_1556
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1654
                        (coe
                           d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0)))))))))
-- Algebra.Structures.IsKleeneAlgebra._.zero
d_zero_2236 ::
  T_IsKleeneAlgebra_2122 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2236 v0
  = coe
      d_zero_1656
      (coe d_isSemiring_2012 (coe d_isIdempotentSemiring_2140 (coe v0)))
-- Algebra.Structures.IsKleeneAlgebra._.zeroʳ
d_zero'691'_2238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
d_zero'691'_2238 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'691'_2238 v9
du_zero'691'_2238 :: T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
du_zero'691'_2238 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (coe
            du_zero'691'_1426 (coe du_isSemiringWithoutOne_1730 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.zeroˡ
d_zero'737'_2240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
d_zero'737'_2240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'737'_2240 v9
du_zero'737'_2240 :: T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
du_zero'737'_2240 v0
  = let v1 = d_isIdempotentSemiring_2140 (coe v0) in
    coe
      (let v2 = d_isSemiring_2012 (coe v1) in
       coe
         (coe
            du_zero'737'_1424 (coe du_isSemiringWithoutOne_1730 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra.starExpansiveˡ
d_starExpansive'737'_2242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
d_starExpansive'737'_2242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_starExpansive'737'_2242 v9
du_starExpansive'737'_2242 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
du_starExpansive'737'_2242 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_starExpansive_2142 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra.starExpansiveʳ
d_starExpansive'691'_2244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
d_starExpansive'691'_2244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_starExpansive'691'_2244 v9
du_starExpansive'691'_2244 ::
  T_IsKleeneAlgebra_2122 -> AgdaAny -> AgdaAny
du_starExpansive'691'_2244 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_starExpansive_2142 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra.starDestructiveˡ
d_starDestructive'737'_2246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_starDestructive'737'_2246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_starDestructive'737'_2246 v9
du_starDestructive'737'_2246 ::
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_starDestructive'737'_2246 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_starDestructive_2144 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra.starDestructiveʳ
d_starDestructive'691'_2248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_starDestructive'691'_2248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_starDestructive'691'_2248 v9
du_starDestructive'691'_2248 ::
  T_IsKleeneAlgebra_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_starDestructive'691'_2248 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_starDestructive_2144 (coe v0))
-- Algebra.Structures.IsQuasiring
d_IsQuasiring_2260 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsQuasiring_2260
  = C_constructor_2358 T_IsMonoid_712
                       (AgdaAny ->
                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsQuasiring.+-isMonoid
d_'43''45'isMonoid_2282 :: T_IsQuasiring_2260 -> T_IsMonoid_712
d_'43''45'isMonoid_2282 v0
  = case coe v0 of
      C_constructor_2358 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring.*-cong
d_'42''45'cong_2284 ::
  T_IsQuasiring_2260 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2284 v0
  = case coe v0 of
      C_constructor_2358 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring.*-assoc
d_'42''45'assoc_2286 ::
  T_IsQuasiring_2260 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2286 v0
  = case coe v0 of
      C_constructor_2358 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring.*-identity
d_'42''45'identity_2288 ::
  T_IsQuasiring_2260 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2288 v0
  = case coe v0 of
      C_constructor_2358 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring.distrib
d_distrib_2290 ::
  T_IsQuasiring_2260 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2290 v0
  = case coe v0 of
      C_constructor_2358 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring.zero
d_zero_2292 ::
  T_IsQuasiring_2260 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2292 v0
  = case coe v0 of
      C_constructor_2358 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring._.assoc
d_assoc_2296 ::
  T_IsQuasiring_2260 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2296 v0
  = coe
      d_assoc_498
      (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_2282 (coe v0)))
-- Algebra.Structures.IsQuasiring._.∙-cong
d_'8729''45'cong_2298 ::
  T_IsQuasiring_2260 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2298 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_2282 (coe v0))))
-- Algebra.Structures.IsQuasiring._.∙-congʳ
d_'8729''45'cong'691'_2300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_2300 v8
du_'8729''45'cong'691'_2300 ::
  T_IsQuasiring_2260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2300 v0
  = let v1 = d_'43''45'isMonoid_2282 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsQuasiring._.∙-congˡ
d_'8729''45'cong'737'_2302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_2302 v8
du_'8729''45'cong'737'_2302 ::
  T_IsQuasiring_2260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2302 v0
  = let v1 = d_'43''45'isMonoid_2282 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsQuasiring._.identity
d_identity_2304 ::
  T_IsQuasiring_2260 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2304 v0
  = coe d_identity_724 (coe d_'43''45'isMonoid_2282 (coe v0))
-- Algebra.Structures.IsQuasiring._.identityʳ
d_identity'691'_2306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
d_identity'691'_2306 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_2306 v8
du_identity'691'_2306 :: T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
du_identity'691'_2306 v0
  = coe du_identity'691'_754 (coe d_'43''45'isMonoid_2282 (coe v0))
-- Algebra.Structures.IsQuasiring._.identityˡ
d_identity'737'_2308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
d_identity'737'_2308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_2308 v8
du_identity'737'_2308 :: T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
du_identity'737'_2308 v0
  = coe du_identity'737'_752 (coe d_'43''45'isMonoid_2282 (coe v0))
-- Algebra.Structures.IsQuasiring._.isMagma
d_isMagma_2310 :: T_IsQuasiring_2260 -> T_IsMagma_178
d_isMagma_2310 v0
  = coe
      d_isMagma_496
      (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_2282 (coe v0)))
-- Algebra.Structures.IsQuasiring._.isSemigroup
d_isSemigroup_2312 :: T_IsQuasiring_2260 -> T_IsSemigroup_488
d_isSemigroup_2312 v0
  = coe d_isSemigroup_722 (coe d_'43''45'isMonoid_2282 (coe v0))
-- Algebra.Structures.IsQuasiring._.isUnitalMagma
d_isUnitalMagma_2314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> T_IsUnitalMagma_666
d_isUnitalMagma_2314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_2314 v8
du_isUnitalMagma_2314 :: T_IsQuasiring_2260 -> T_IsUnitalMagma_666
du_isUnitalMagma_2314 v0
  = coe du_isUnitalMagma_756 (coe d_'43''45'isMonoid_2282 (coe v0))
-- Algebra.Structures.IsQuasiring._.isEquivalence
d_isEquivalence_2316 ::
  T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2316 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_2282 (coe v0))))
-- Algebra.Structures.IsQuasiring._.isPartialEquivalence
d_isPartialEquivalence_2318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_2318 v8
du_isPartialEquivalence_2318 ::
  T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2318 v0
  = let v1 = d_'43''45'isMonoid_2282 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.IsQuasiring._.refl
d_refl_2320 :: T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
d_refl_2320 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_2282 (coe v0)))))
-- Algebra.Structures.IsQuasiring._.reflexive
d_reflexive_2322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2260 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_2322 v8
du_reflexive_2322 ::
  T_IsQuasiring_2260 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2322 v0
  = let v1 = d_'43''45'isMonoid_2282 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_186 (coe v3)) v4)))
-- Algebra.Structures.IsQuasiring._.setoid
d_setoid_2324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_2324 v8
du_setoid_2324 ::
  T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2324 v0
  = let v1 = d_'43''45'isMonoid_2282 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe (coe du_setoid_202 (coe d_isMagma_496 (coe v2))))
-- Algebra.Structures.IsQuasiring._.sym
d_sym_2326 ::
  T_IsQuasiring_2260 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2326 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_2282 (coe v0)))))
-- Algebra.Structures.IsQuasiring._.trans
d_trans_2328 ::
  T_IsQuasiring_2260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2328 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_2282 (coe v0)))))
-- Algebra.Structures.IsQuasiring.distribˡ
d_distrib'737'_2330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2260 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_2330 v8
du_distrib'737'_2330 ::
  T_IsQuasiring_2260 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2330 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_distrib_2290 (coe v0))
-- Algebra.Structures.IsQuasiring.distribʳ
d_distrib'691'_2332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2260 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_2332 v8
du_distrib'691'_2332 ::
  T_IsQuasiring_2260 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2332 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_distrib_2290 (coe v0))
-- Algebra.Structures.IsQuasiring.zeroˡ
d_zero'737'_2334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
d_zero'737'_2334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'737'_2334 v8
du_zero'737'_2334 :: T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
du_zero'737'_2334 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_zero_2292 (coe v0))
-- Algebra.Structures.IsQuasiring.zeroʳ
d_zero'691'_2336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
d_zero'691'_2336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'691'_2336 v8
du_zero'691'_2336 :: T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
du_zero'691'_2336 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_zero_2292 (coe v0))
-- Algebra.Structures.IsQuasiring.identityˡ
d_identity'737'_2338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
d_identity'737'_2338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_2338 v8
du_identity'737'_2338 :: T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
du_identity'737'_2338 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_'42''45'identity_2288 (coe v0))
-- Algebra.Structures.IsQuasiring.identityʳ
d_identity'691'_2340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
d_identity'691'_2340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_2340 v8
du_identity'691'_2340 :: T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
du_identity'691'_2340 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_'42''45'identity_2288 (coe v0))
-- Algebra.Structures.IsQuasiring.*-isMagma
d_'42''45'isMagma_2342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> T_IsMagma_178
d_'42''45'isMagma_2342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_2342 v8
du_'42''45'isMagma_2342 :: T_IsQuasiring_2260 -> T_IsMagma_178
du_'42''45'isMagma_2342 v0
  = coe
      C_constructor_210
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe d_isSemigroup_722 (coe d_'43''45'isMonoid_2282 (coe v0)))))
      (coe d_'42''45'cong_2284 (coe v0))
-- Algebra.Structures.IsQuasiring.*-isSemigroup
d_'42''45'isSemigroup_2344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> T_IsSemigroup_488
d_'42''45'isSemigroup_2344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_2344 v8
du_'42''45'isSemigroup_2344 ::
  T_IsQuasiring_2260 -> T_IsSemigroup_488
du_'42''45'isSemigroup_2344 v0
  = coe
      C_constructor_522 (coe du_'42''45'isMagma_2342 (coe v0))
      (coe d_'42''45'assoc_2286 (coe v0))
-- Algebra.Structures.IsQuasiring.*-isMonoid
d_'42''45'isMonoid_2346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> T_IsMonoid_712
d_'42''45'isMonoid_2346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_2346 v8
du_'42''45'isMonoid_2346 :: T_IsQuasiring_2260 -> T_IsMonoid_712
du_'42''45'isMonoid_2346 v0
  = coe
      C_constructor_758 (coe du_'42''45'isSemigroup_2344 (coe v0))
      (coe d_'42''45'identity_2288 (coe v0))
-- Algebra.Structures.IsQuasiring._.∙-congʳ
d_'8729''45'cong'691'_2350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_2350 v8
du_'8729''45'cong'691'_2350 ::
  T_IsQuasiring_2260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2350 v0
  = let v1 = coe du_'42''45'isMonoid_2346 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsQuasiring._.∙-congˡ
d_'8729''45'cong'737'_2352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_2352 v8
du_'8729''45'cong'737'_2352 ::
  T_IsQuasiring_2260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2352 v0
  = let v1 = coe du_'42''45'isMonoid_2346 (coe v0) in
    coe
      (let v2 = d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = d_isMagma_496 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsQuasiring._.identityʳ
d_identity'691'_2354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
d_identity'691'_2354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_2354 v8
du_identity'691'_2354 :: T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
du_identity'691'_2354 v0
  = coe du_identity'691'_754 (coe du_'42''45'isMonoid_2346 (coe v0))
-- Algebra.Structures.IsQuasiring._.identityˡ
d_identity'737'_2356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
d_identity'737'_2356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_2356 v8
du_identity'737'_2356 :: T_IsQuasiring_2260 -> AgdaAny -> AgdaAny
du_identity'737'_2356 v0
  = coe du_identity'737'_752 (coe du_'42''45'isMonoid_2346 (coe v0))
-- Algebra.Structures.IsRingWithoutOne
d_IsRingWithoutOne_2368 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsRingWithoutOne_2368
  = C_constructor_2482 T_IsAbelianGroup_1172
                       (AgdaAny ->
                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsRingWithoutOne.+-isAbelianGroup
d_'43''45'isAbelianGroup_2386 ::
  T_IsRingWithoutOne_2368 -> T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2386 v0
  = case coe v0 of
      C_constructor_2482 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRingWithoutOne.*-cong
d_'42''45'cong_2388 ::
  T_IsRingWithoutOne_2368 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2388 v0
  = case coe v0 of
      C_constructor_2482 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRingWithoutOne.*-assoc
d_'42''45'assoc_2390 ::
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2390 v0
  = case coe v0 of
      C_constructor_2482 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRingWithoutOne.distrib
d_distrib_2392 ::
  T_IsRingWithoutOne_2368 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2392 v0
  = case coe v0 of
      C_constructor_2482 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRingWithoutOne._._//_
d__'47''47'__2396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__2396 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du__'47''47'__2396 v4 v6
du__'47''47'__2396 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__2396 v0 v1 = coe du__'47''47'__1136 (coe v0) (coe v1)
-- Algebra.Structures.IsRingWithoutOne._.assoc
d_assoc_2398 ::
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2398 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_1088
            (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0)))))
-- Algebra.Structures.IsRingWithoutOne._.comm
d_comm_2400 ::
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2400 v0
  = coe d_comm_1186 (coe d_'43''45'isAbelianGroup_2386 (coe v0))
-- Algebra.Structures.IsRingWithoutOne._.∙-cong
d_'8729''45'cong_2402 ::
  T_IsRingWithoutOne_2368 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2402 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_1088
               (coe
                  d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0))))))
-- Algebra.Structures.IsRingWithoutOne._.∙-congʳ
d_'8729''45'cong'691'_2404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_2404 v8
du_'8729''45'cong'691'_2404 ::
  T_IsRingWithoutOne_2368 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2404 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe
         (let v3 = d_isMonoid_1088 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsRingWithoutOne._.∙-congˡ
d_'8729''45'cong'737'_2406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_2406 v8
du_'8729''45'cong'737'_2406 ::
  T_IsRingWithoutOne_2368 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2406 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe
         (let v3 = d_isMonoid_1088 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsRingWithoutOne._.identity
d_identity_2408 ::
  T_IsRingWithoutOne_2368 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2408 v0
  = coe
      d_identity_724
      (coe
         d_isMonoid_1088
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0))))
-- Algebra.Structures.IsRingWithoutOne._.identityʳ
d_identity'691'_2410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
d_identity'691'_2410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_2410 v8
du_identity'691'_2410 ::
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
du_identity'691'_2410 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe (coe du_identity'691'_754 (coe d_isMonoid_1088 (coe v2))))
-- Algebra.Structures.IsRingWithoutOne._.identityˡ
d_identity'737'_2412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
d_identity'737'_2412 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_2412 v8
du_identity'737'_2412 ::
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
du_identity'737'_2412 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe (coe du_identity'737'_752 (coe d_isMonoid_1088 (coe v2))))
-- Algebra.Structures.IsRingWithoutOne._.isCommutativeMagma
d_isCommutativeMagma_2414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_2414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_2414 v8
du_isCommutativeMagma_2414 ::
  T_IsRingWithoutOne_2368 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_2414 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe
      (let v2 = coe du_isCommutativeMonoid_1244 (coe v1) in
       coe
         (coe
            du_isCommutativeMagma_606
            (coe du_isCommutativeSemigroup_814 (coe v2))))
-- Algebra.Structures.IsRingWithoutOne._.isCommutativeMonoid
d_isCommutativeMonoid_2416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2416 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMonoid_2416 v8
du_isCommutativeMonoid_2416 ::
  T_IsRingWithoutOne_2368 -> T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2416 v0
  = coe
      du_isCommutativeMonoid_1244
      (coe d_'43''45'isAbelianGroup_2386 (coe v0))
-- Algebra.Structures.IsRingWithoutOne._.isCommutativeSemigroup
d_isCommutativeSemigroup_2418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_2418 v8
du_isCommutativeSemigroup_2418 ::
  T_IsRingWithoutOne_2368 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2418 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe
      (coe
         du_isCommutativeSemigroup_814
         (coe du_isCommutativeMonoid_1244 (coe v1)))
-- Algebra.Structures.IsRingWithoutOne._.isGroup
d_isGroup_2420 :: T_IsRingWithoutOne_2368 -> T_IsGroup_1074
d_isGroup_2420 v0
  = coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0))
-- Algebra.Structures.IsRingWithoutOne._.isInvertibleMagma
d_isInvertibleMagma_2422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> T_IsInvertibleMagma_958
d_isInvertibleMagma_2422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isInvertibleMagma_2422 v8
du_isInvertibleMagma_2422 ::
  T_IsRingWithoutOne_2368 -> T_IsInvertibleMagma_958
du_isInvertibleMagma_2422 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe (coe du_isInvertibleMagma_1160 (coe d_isGroup_1184 (coe v1)))
-- Algebra.Structures.IsRingWithoutOne._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 -> T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_2424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isInvertibleUnitalMagma_2424 v8
du_isInvertibleUnitalMagma_2424 ::
  T_IsRingWithoutOne_2368 -> T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_2424 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe
      (coe du_isInvertibleUnitalMagma_1162 (coe d_isGroup_1184 (coe v1)))
-- Algebra.Structures.IsRingWithoutOne._.isMagma
d_isMagma_2426 :: T_IsRingWithoutOne_2368 -> T_IsMagma_178
d_isMagma_2426 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_1088
            (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0)))))
-- Algebra.Structures.IsRingWithoutOne._.isMonoid
d_isMonoid_2428 :: T_IsRingWithoutOne_2368 -> T_IsMonoid_712
d_isMonoid_2428 v0
  = coe
      d_isMonoid_1088
      (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0)))
-- Algebra.Structures.IsRingWithoutOne._.isSemigroup
d_isSemigroup_2430 :: T_IsRingWithoutOne_2368 -> T_IsSemigroup_488
d_isSemigroup_2430 v0
  = coe
      d_isSemigroup_722
      (coe
         d_isMonoid_1088
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0))))
-- Algebra.Structures.IsRingWithoutOne._.isUnitalMagma
d_isUnitalMagma_2432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> T_IsUnitalMagma_666
d_isUnitalMagma_2432 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_2432 v8
du_isUnitalMagma_2432 ::
  T_IsRingWithoutOne_2368 -> T_IsUnitalMagma_666
du_isUnitalMagma_2432 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe (coe du_isUnitalMagma_756 (coe d_isMonoid_1088 (coe v2))))
-- Algebra.Structures.IsRingWithoutOne._.⁻¹-cong
d_'8315''185''45'cong_2434 ::
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_2434 v0
  = coe
      d_'8315''185''45'cong_1092
      (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0)))
-- Algebra.Structures.IsRingWithoutOne._.inverse
d_inverse_2436 ::
  T_IsRingWithoutOne_2368 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2436 v0
  = coe
      d_inverse_1090
      (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0)))
-- Algebra.Structures.IsRingWithoutOne._.inverseʳ
d_inverse'691'_2438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
d_inverse'691'_2438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_inverse'691'_2438 v8
du_inverse'691'_2438 ::
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
du_inverse'691'_2438 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe (coe du_inverse'691'_1146 (coe d_isGroup_1184 (coe v1)))
-- Algebra.Structures.IsRingWithoutOne._.inverseˡ
d_inverse'737'_2440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
d_inverse'737'_2440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_inverse'737'_2440 v8
du_inverse'737'_2440 ::
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
du_inverse'737'_2440 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe (coe du_inverse'737'_1144 (coe d_isGroup_1184 (coe v1)))
-- Algebra.Structures.IsRingWithoutOne._.isEquivalence
d_isEquivalence_2442 ::
  T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2442 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_1088
               (coe
                  d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0))))))
-- Algebra.Structures.IsRingWithoutOne._.isPartialEquivalence
d_isPartialEquivalence_2444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_2444 v8
du_isPartialEquivalence_2444 ::
  T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2444 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe
         (let v3 = d_isMonoid_1088 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                     (coe d_isEquivalence_186 (coe v5)))))))
-- Algebra.Structures.IsRingWithoutOne._.refl
d_refl_2446 :: T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
d_refl_2446 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0)))))))
-- Algebra.Structures.IsRingWithoutOne._.reflexive
d_reflexive_2448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2448 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_2448 v8
du_reflexive_2448 ::
  T_IsRingWithoutOne_2368 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2448 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe
         (let v3 = d_isMonoid_1088 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                       (coe d_isEquivalence_186 (coe v5)) v6)))))
-- Algebra.Structures.IsRingWithoutOne._.setoid
d_setoid_2450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_2450 v8
du_setoid_2450 ::
  T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2450 v0
  = let v1 = d_'43''45'isAbelianGroup_2386 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe
         (let v3 = d_isMonoid_1088 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe (coe du_setoid_202 (coe d_isMagma_496 (coe v4))))))
-- Algebra.Structures.IsRingWithoutOne._.sym
d_sym_2452 ::
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2452 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0)))))))
-- Algebra.Structures.IsRingWithoutOne._.trans
d_trans_2454 ::
  T_IsRingWithoutOne_2368 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2454 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v0)))))))
-- Algebra.Structures.IsRingWithoutOne._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_2456 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8
  = du_unique'691''45''8315''185'_2456 v4 v6 v7 v8
du_unique'691''45''8315''185'_2456 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_2456 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_2386 (coe v3) in
    coe
      (coe
         du_unique'691''45''8315''185'_1158 (coe v0) (coe v2) (coe v1)
         (coe d_isGroup_1184 (coe v4)))
-- Algebra.Structures.IsRingWithoutOne._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_2458 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8
  = du_unique'737''45''8315''185'_2458 v4 v6 v7 v8
du_unique'737''45''8315''185'_2458 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_2458 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_2386 (coe v3) in
    coe
      (coe
         du_unique'737''45''8315''185'_1152 (coe v0) (coe v2) (coe v1)
         (coe d_isGroup_1184 (coe v4)))
-- Algebra.Structures.IsRingWithoutOne.distribˡ
d_distrib'737'_2460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_2460 v8
du_distrib'737'_2460 ::
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2460 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_distrib_2392 (coe v0))
-- Algebra.Structures.IsRingWithoutOne.distribʳ
d_distrib'691'_2462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2462 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_2462 v8
du_distrib'691'_2462 ::
  T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2462 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_distrib_2392 (coe v0))
-- Algebra.Structures.IsRingWithoutOne.zeroˡ
d_zero'737'_2464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
d_zero'737'_2464 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_zero'737'_2464 v4 v5 v6 v7 v8
du_zero'737'_2464 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
du_zero'737'_2464 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'distrib'691''8743'id'691''8743'inv'691''8658'ze'737'_644
      (coe
         du_setoid_202
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v4)))))))
      (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         d_'8729''45'cong_188
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v4)))))))
      (coe d_'42''45'cong_2388 (coe v4))
      (coe
         d_assoc_498
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_1088
               (coe
                  d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v4))))))
      (coe du_distrib'691'_2462 (coe v4))
      (coe
         du_identity'691'_754
         (coe
            d_isMonoid_1088
            (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v4)))))
      (coe
         du_inverse'691'_1146
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v4))))
-- Algebra.Structures.IsRingWithoutOne.zeroʳ
d_zero'691'_2466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
d_zero'691'_2466 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_zero'691'_2466 v4 v5 v6 v7 v8
du_zero'691'_2466 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> AgdaAny -> AgdaAny
du_zero'691'_2466 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'distrib'737''8743'id'691''8743'inv'691''8658'ze'691'_656
      (coe
         du_setoid_202
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v4)))))))
      (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         d_'8729''45'cong_188
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v4)))))))
      (coe d_'42''45'cong_2388 (coe v4))
      (coe
         d_assoc_498
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_1088
               (coe
                  d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v4))))))
      (coe du_distrib'737'_2460 (coe v4))
      (coe
         du_identity'691'_754
         (coe
            d_isMonoid_1088
            (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v4)))))
      (coe
         du_inverse'691'_1146
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v4))))
-- Algebra.Structures.IsRingWithoutOne.zero
d_zero_2468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2468 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_zero_2468 v4 v5 v6 v7 v8
du_zero_2468 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_2468 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_zero'737'_2464 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      (coe
         du_zero'691'_2466 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Structures.IsRingWithoutOne.isNearSemiring
d_isNearSemiring_2470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> T_IsNearSemiring_1260
d_isNearSemiring_2470 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_isNearSemiring_2470 v4 v5 v6 v7 v8
du_isNearSemiring_2470 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> T_IsNearSemiring_1260
du_isNearSemiring_2470 v0 v1 v2 v3 v4
  = coe
      C_constructor_1334
      (coe
         d_isMonoid_1088
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2386 (coe v4))))
      (coe d_'42''45'cong_2388 (coe v4))
      (coe d_'42''45'assoc_2390 (coe v4))
      (coe du_distrib'691'_2462 (coe v4))
      (coe
         du_zero'737'_2464 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Structures.IsRingWithoutOne._.∙-congʳ
d_'8729''45'cong'691'_2474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2474 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_'8729''45'cong'691'_2474 v4 v5 v6 v7 v8
du_'8729''45'cong'691'_2474 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2474 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
              (coe v4) in
    coe
      (let v6 = coe du_'42''45'isMagma_1324 (coe v5) in
       coe
         (let v7 = coe du_setoid_202 (coe v6) in
          coe
            (let v8 = d_'8729''45'cong_188 (coe v6) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                  (coe v8)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v7)))))))
-- Algebra.Structures.IsRingWithoutOne._.∙-congˡ
d_'8729''45'cong'737'_2476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2476 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_'8729''45'cong'737'_2476 v4 v5 v6 v7 v8
du_'8729''45'cong'737'_2476 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2368 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2476 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
              (coe v4) in
    coe
      (let v6 = coe du_'42''45'isMagma_1324 (coe v5) in
       coe
         (let v7 = coe du_setoid_202 (coe v6) in
          coe
            (let v8 = d_'8729''45'cong_188 (coe v6) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                  (coe v8)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v7)))))))
-- Algebra.Structures.IsRingWithoutOne._.*-isMagma
d_'42''45'isMagma_2478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> T_IsMagma_178
d_'42''45'isMagma_2478 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_'42''45'isMagma_2478 v4 v5 v6 v7 v8
du_'42''45'isMagma_2478 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> T_IsMagma_178
du_'42''45'isMagma_2478 v0 v1 v2 v3 v4
  = coe
      du_'42''45'isMagma_1324
      (coe
         du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Algebra.Structures.IsRingWithoutOne._.*-isSemigroup
d_'42''45'isSemigroup_2480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> T_IsSemigroup_488
d_'42''45'isSemigroup_2480 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_'42''45'isSemigroup_2480 v4 v5 v6 v7 v8
du_'42''45'isSemigroup_2480 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2368 -> T_IsSemigroup_488
du_'42''45'isSemigroup_2480 v0 v1 v2 v3 v4
  = coe
      du_'42''45'isSemigroup_1326
      (coe
         du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Algebra.Structures.IsNonAssociativeRing
d_IsNonAssociativeRing_2494 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsNonAssociativeRing_2494
  = C_constructor_2614 T_IsAbelianGroup_1172
                       (AgdaAny ->
                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsNonAssociativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2516 ::
  T_IsNonAssociativeRing_2494 -> T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2516 v0
  = case coe v0 of
      C_constructor_2614 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNonAssociativeRing.*-cong
d_'42''45'cong_2518 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2518 v0
  = case coe v0 of
      C_constructor_2614 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNonAssociativeRing.*-identity
d_'42''45'identity_2520 ::
  T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2520 v0
  = case coe v0 of
      C_constructor_2614 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNonAssociativeRing.distrib
d_distrib_2522 ::
  T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2522 v0
  = case coe v0 of
      C_constructor_2614 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNonAssociativeRing.zero
d_zero_2524 ::
  T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2524 v0
  = case coe v0 of
      C_constructor_2614 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNonAssociativeRing._._//_
d__'47''47'__2528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__2528 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du__'47''47'__2528 v4 v6
du__'47''47'__2528 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__2528 v0 v1 = coe du__'47''47'__1136 (coe v0) (coe v1)
-- Algebra.Structures.IsNonAssociativeRing._.assoc
d_assoc_2530 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2530 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_1088
            (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0)))))
-- Algebra.Structures.IsNonAssociativeRing._.comm
d_comm_2532 ::
  T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2532 v0
  = coe d_comm_1186 (coe d_'43''45'isAbelianGroup_2516 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing._.∙-cong
d_'8729''45'cong_2534 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2534 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_1088
               (coe
                  d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0))))))
-- Algebra.Structures.IsNonAssociativeRing._.∙-congʳ
d_'8729''45'cong'691'_2536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2536 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2536 v9
du_'8729''45'cong'691'_2536 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2536 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe
         (let v3 = d_isMonoid_1088 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsNonAssociativeRing._.∙-congˡ
d_'8729''45'cong'737'_2538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2538 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2538 v9
du_'8729''45'cong'737'_2538 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2538 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe
         (let v3 = d_isMonoid_1088 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (let v6 = coe du_setoid_202 (coe v5) in
                   coe
                     (let v7 = d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.IsNonAssociativeRing._.identity
d_identity_2540 ::
  T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2540 v0
  = coe
      d_identity_724
      (coe
         d_isMonoid_1088
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0))))
-- Algebra.Structures.IsNonAssociativeRing._.identityʳ
d_identity'691'_2542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
d_identity'691'_2542 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2542 v9
du_identity'691'_2542 ::
  T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
du_identity'691'_2542 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe (coe du_identity'691'_754 (coe d_isMonoid_1088 (coe v2))))
-- Algebra.Structures.IsNonAssociativeRing._.identityˡ
d_identity'737'_2544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
d_identity'737'_2544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2544 v9
du_identity'737'_2544 ::
  T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
du_identity'737'_2544 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe (coe du_identity'737'_752 (coe d_isMonoid_1088 (coe v2))))
-- Algebra.Structures.IsNonAssociativeRing._.isCommutativeMagma
d_isCommutativeMagma_2546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_2546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_2546 v9
du_isCommutativeMagma_2546 ::
  T_IsNonAssociativeRing_2494 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_2546 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe
      (let v2 = coe du_isCommutativeMonoid_1244 (coe v1) in
       coe
         (coe
            du_isCommutativeMagma_606
            (coe du_isCommutativeSemigroup_814 (coe v2))))
-- Algebra.Structures.IsNonAssociativeRing._.isCommutativeMonoid
d_isCommutativeMonoid_2548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2548 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMonoid_2548 v9
du_isCommutativeMonoid_2548 ::
  T_IsNonAssociativeRing_2494 -> T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2548 v0
  = coe
      du_isCommutativeMonoid_1244
      (coe d_'43''45'isAbelianGroup_2516 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing._.isCommutativeSemigroup
d_isCommutativeSemigroup_2550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              v9
  = du_isCommutativeSemigroup_2550 v9
du_isCommutativeSemigroup_2550 ::
  T_IsNonAssociativeRing_2494 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2550 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe
      (coe
         du_isCommutativeSemigroup_814
         (coe du_isCommutativeMonoid_1244 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing._.isGroup
d_isGroup_2552 :: T_IsNonAssociativeRing_2494 -> T_IsGroup_1074
d_isGroup_2552 v0
  = coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing._.isInvertibleMagma
d_isInvertibleMagma_2554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> T_IsInvertibleMagma_958
d_isInvertibleMagma_2554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isInvertibleMagma_2554 v9
du_isInvertibleMagma_2554 ::
  T_IsNonAssociativeRing_2494 -> T_IsInvertibleMagma_958
du_isInvertibleMagma_2554 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe (coe du_isInvertibleMagma_1160 (coe d_isGroup_1184 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 -> T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_2556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_isInvertibleUnitalMagma_2556 v9
du_isInvertibleUnitalMagma_2556 ::
  T_IsNonAssociativeRing_2494 -> T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_2556 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe
      (coe du_isInvertibleUnitalMagma_1162 (coe d_isGroup_1184 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing._.isMagma
d_isMagma_2558 :: T_IsNonAssociativeRing_2494 -> T_IsMagma_178
d_isMagma_2558 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_1088
            (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0)))))
-- Algebra.Structures.IsNonAssociativeRing._.isMonoid
d_isMonoid_2560 :: T_IsNonAssociativeRing_2494 -> T_IsMonoid_712
d_isMonoid_2560 v0
  = coe
      d_isMonoid_1088
      (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0)))
-- Algebra.Structures.IsNonAssociativeRing._.isSemigroup
d_isSemigroup_2562 ::
  T_IsNonAssociativeRing_2494 -> T_IsSemigroup_488
d_isSemigroup_2562 v0
  = coe
      d_isSemigroup_722
      (coe
         d_isMonoid_1088
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0))))
-- Algebra.Structures.IsNonAssociativeRing._.isUnitalMagma
d_isUnitalMagma_2564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> T_IsUnitalMagma_666
d_isUnitalMagma_2564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_2564 v9
du_isUnitalMagma_2564 ::
  T_IsNonAssociativeRing_2494 -> T_IsUnitalMagma_666
du_isUnitalMagma_2564 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe (coe du_isUnitalMagma_756 (coe d_isMonoid_1088 (coe v2))))
-- Algebra.Structures.IsNonAssociativeRing._.⁻¹-cong
d_'8315''185''45'cong_2566 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_2566 v0
  = coe
      d_'8315''185''45'cong_1092
      (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0)))
-- Algebra.Structures.IsNonAssociativeRing._.inverse
d_inverse_2568 ::
  T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2568 v0
  = coe
      d_inverse_1090
      (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0)))
-- Algebra.Structures.IsNonAssociativeRing._.inverseʳ
d_inverse'691'_2570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
d_inverse'691'_2570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'691'_2570 v9
du_inverse'691'_2570 ::
  T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
du_inverse'691'_2570 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe (coe du_inverse'691'_1146 (coe d_isGroup_1184 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing._.inverseˡ
d_inverse'737'_2572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
d_inverse'737'_2572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'737'_2572 v9
du_inverse'737'_2572 ::
  T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
du_inverse'737'_2572 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe (coe du_inverse'737'_1144 (coe d_isGroup_1184 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing._.isEquivalence
d_isEquivalence_2574 ::
  T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2574 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_1088
               (coe
                  d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0))))))
-- Algebra.Structures.IsNonAssociativeRing._.isPartialEquivalence
d_isPartialEquivalence_2576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2576 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_2576 v9
du_isPartialEquivalence_2576 ::
  T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2576 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe
         (let v3 = d_isMonoid_1088 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                     (coe d_isEquivalence_186 (coe v5)))))))
-- Algebra.Structures.IsNonAssociativeRing._.refl
d_refl_2578 :: T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
d_refl_2578 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0)))))))
-- Algebra.Structures.IsNonAssociativeRing._.reflexive
d_reflexive_2580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_2580 v9
du_reflexive_2580 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2580 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe
         (let v3 = d_isMonoid_1088 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = d_isMagma_496 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                       (coe d_isEquivalence_186 (coe v5)) v6)))))
-- Algebra.Structures.IsNonAssociativeRing._.setoid
d_setoid_2582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2582 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_2582 v9
du_setoid_2582 ::
  T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2582 v0
  = let v1 = d_'43''45'isAbelianGroup_2516 (coe v0) in
    coe
      (let v2 = d_isGroup_1184 (coe v1) in
       coe
         (let v3 = d_isMonoid_1088 (coe v2) in
          coe
            (let v4 = d_isSemigroup_722 (coe v3) in
             coe (coe du_setoid_202 (coe d_isMagma_496 (coe v4))))))
-- Algebra.Structures.IsNonAssociativeRing._.sym
d_sym_2584 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2584 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0)))))))
-- Algebra.Structures.IsNonAssociativeRing._.trans
d_trans_2586 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2586 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0)))))))
-- Algebra.Structures.IsNonAssociativeRing._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_2588 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'691''45''8315''185'_2588 v4 v6 v7 v9
du_unique'691''45''8315''185'_2588 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_2588 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_2516 (coe v3) in
    coe
      (coe
         du_unique'691''45''8315''185'_1158 (coe v0) (coe v2) (coe v1)
         (coe d_isGroup_1184 (coe v4)))
-- Algebra.Structures.IsNonAssociativeRing._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_2590 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'737''45''8315''185'_2590 v4 v6 v7 v9
du_unique'737''45''8315''185'_2590 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_2590 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_2516 (coe v3) in
    coe
      (coe
         du_unique'737''45''8315''185'_1152 (coe v0) (coe v2) (coe v1)
         (coe d_isGroup_1184 (coe v4)))
-- Algebra.Structures.IsNonAssociativeRing.zeroˡ
d_zero'737'_2592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
d_zero'737'_2592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'737'_2592 v9
du_zero'737'_2592 ::
  T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
du_zero'737'_2592 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_zero_2524 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.zeroʳ
d_zero'691'_2594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
d_zero'691'_2594 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'691'_2594 v9
du_zero'691'_2594 ::
  T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
du_zero'691'_2594 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_zero_2524 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.distribˡ
d_distrib'737'_2596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'737'_2596 v9
du_distrib'737'_2596 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2596 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_distrib_2522 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.distribʳ
d_distrib'691'_2598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2598 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'691'_2598 v9
du_distrib'691'_2598 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2598 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_distrib_2522 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.*-isMagma
d_'42''45'isMagma_2600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsNonAssociativeRing_2494 -> T_IsMagma_178
d_'42''45'isMagma_2600 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMagma_2600 v9
du_'42''45'isMagma_2600 ::
  T_IsNonAssociativeRing_2494 -> T_IsMagma_178
du_'42''45'isMagma_2600 v0
  = coe
      C_constructor_210
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2516 (coe v0)))))))
      (coe d_'42''45'cong_2518 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.*-identityˡ
d_'42''45'identity'737'_2602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
d_'42''45'identity'737'_2602 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'identity'737'_2602 v9
du_'42''45'identity'737'_2602 ::
  T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
du_'42''45'identity'737'_2602 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_'42''45'identity_2520 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.*-identityʳ
d_'42''45'identity'691'_2604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
d_'42''45'identity'691'_2604 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'identity'691'_2604 v9
du_'42''45'identity'691'_2604 ::
  T_IsNonAssociativeRing_2494 -> AgdaAny -> AgdaAny
du_'42''45'identity'691'_2604 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_'42''45'identity_2520 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.*-isUnitalMagma
d_'42''45'isUnitalMagma_2606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2494 -> T_IsUnitalMagma_666
d_'42''45'isUnitalMagma_2606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isUnitalMagma_2606 v9
du_'42''45'isUnitalMagma_2606 ::
  T_IsNonAssociativeRing_2494 -> T_IsUnitalMagma_666
du_'42''45'isUnitalMagma_2606 v0
  = coe
      C_constructor_706 (coe du_'42''45'isMagma_2600 (coe v0))
      (coe d_'42''45'identity_2520 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing._.∙-congʳ
d_'8729''45'cong'691'_2610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2610 v9
du_'8729''45'cong'691'_2610 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2610 v0
  = let v1 = coe du_'42''45'isUnitalMagma_2606 (coe v0) in
    coe
      (let v2 = d_isMagma_676 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsNonAssociativeRing._.∙-congˡ
d_'8729''45'cong'737'_2612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2612 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2612 v9
du_'8729''45'cong'737'_2612 ::
  T_IsNonAssociativeRing_2494 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2612 v0
  = let v1 = coe du_'42''45'isUnitalMagma_2606 (coe v0) in
    coe
      (let v2 = d_isMagma_676 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsNearring
d_IsNearring_2626 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsNearring_2626
  = C_constructor_2728 T_IsQuasiring_2260
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsNearring.isQuasiring
d_isQuasiring_2644 :: T_IsNearring_2626 -> T_IsQuasiring_2260
d_isQuasiring_2644 v0
  = case coe v0 of
      C_constructor_2728 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearring.+-inverse
d_'43''45'inverse_2646 ::
  T_IsNearring_2626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_2646 v0
  = case coe v0 of
      C_constructor_2728 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearring.⁻¹-cong
d_'8315''185''45'cong_2648 ::
  T_IsNearring_2626 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_2648 v0
  = case coe v0 of
      C_constructor_2728 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearring._.*-assoc
d_'42''45'assoc_2652 ::
  T_IsNearring_2626 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2652 v0
  = coe d_'42''45'assoc_2286 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.*-cong
d_'42''45'cong_2654 ::
  T_IsNearring_2626 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2654 v0
  = coe d_'42''45'cong_2284 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.∙-congʳ
d_'8729''45'cong'691'_2656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2626 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2656 v9
du_'8729''45'cong'691'_2656 ::
  T_IsNearring_2626 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2656 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isMonoid_2346 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsNearring._.∙-congˡ
d_'8729''45'cong'737'_2658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2626 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2658 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2658 v9
du_'8729''45'cong'737'_2658 ::
  T_IsNearring_2626 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2658 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isMonoid_2346 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsNearring._.*-identity
d_'42''45'identity_2660 ::
  T_IsNearring_2626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2660 v0
  = coe d_'42''45'identity_2288 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.identityʳ
d_identity'691'_2662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> AgdaAny -> AgdaAny
d_identity'691'_2662 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2662 v9
du_identity'691'_2662 :: T_IsNearring_2626 -> AgdaAny -> AgdaAny
du_identity'691'_2662 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (coe du_identity'691'_754 (coe du_'42''45'isMonoid_2346 (coe v1)))
-- Algebra.Structures.IsNearring._.identityˡ
d_identity'737'_2664 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> AgdaAny -> AgdaAny
d_identity'737'_2664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2664 v9
du_identity'737'_2664 :: T_IsNearring_2626 -> AgdaAny -> AgdaAny
du_identity'737'_2664 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (coe du_identity'737'_752 (coe du_'42''45'isMonoid_2346 (coe v1)))
-- Algebra.Structures.IsNearring._.*-isMagma
d_'42''45'isMagma_2666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> T_IsMagma_178
d_'42''45'isMagma_2666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMagma_2666 v9
du_'42''45'isMagma_2666 :: T_IsNearring_2626 -> T_IsMagma_178
du_'42''45'isMagma_2666 v0
  = coe du_'42''45'isMagma_2342 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.*-isMonoid
d_'42''45'isMonoid_2668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> T_IsMonoid_712
d_'42''45'isMonoid_2668 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMonoid_2668 v9
du_'42''45'isMonoid_2668 :: T_IsNearring_2626 -> T_IsMonoid_712
du_'42''45'isMonoid_2668 v0
  = coe du_'42''45'isMonoid_2346 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.*-isSemigroup
d_'42''45'isSemigroup_2670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> T_IsSemigroup_488
d_'42''45'isSemigroup_2670 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isSemigroup_2670 v9
du_'42''45'isSemigroup_2670 ::
  T_IsNearring_2626 -> T_IsSemigroup_488
du_'42''45'isSemigroup_2670 v0
  = coe du_'42''45'isSemigroup_2344 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.assoc
d_assoc_2672 ::
  T_IsNearring_2626 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2672 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe d_'43''45'isMonoid_2282 (coe d_isQuasiring_2644 (coe v0))))
-- Algebra.Structures.IsNearring._.∙-cong
d_'8729''45'cong_2674 ::
  T_IsNearring_2626 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2674 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe d_'43''45'isMonoid_2282 (coe d_isQuasiring_2644 (coe v0)))))
-- Algebra.Structures.IsNearring._.∙-congʳ
d_'8729''45'cong'691'_2676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2626 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2676 v9
du_'8729''45'cong'691'_2676 ::
  T_IsNearring_2626 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2676 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (let v2 = d_'43''45'isMonoid_2282 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsNearring._.∙-congˡ
d_'8729''45'cong'737'_2678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2626 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2678 v9
du_'8729''45'cong'737'_2678 ::
  T_IsNearring_2626 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2678 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (let v2 = d_'43''45'isMonoid_2282 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsNearring._.identity
d_identity_2680 ::
  T_IsNearring_2626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2680 v0
  = coe
      d_identity_724
      (coe d_'43''45'isMonoid_2282 (coe d_isQuasiring_2644 (coe v0)))
-- Algebra.Structures.IsNearring._.identityʳ
d_identity'691'_2682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> AgdaAny -> AgdaAny
d_identity'691'_2682 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2682 v9
du_identity'691'_2682 :: T_IsNearring_2626 -> AgdaAny -> AgdaAny
du_identity'691'_2682 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (coe du_identity'691'_754 (coe d_'43''45'isMonoid_2282 (coe v1)))
-- Algebra.Structures.IsNearring._.identityˡ
d_identity'737'_2684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> AgdaAny -> AgdaAny
d_identity'737'_2684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2684 v9
du_identity'737'_2684 :: T_IsNearring_2626 -> AgdaAny -> AgdaAny
du_identity'737'_2684 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (coe du_identity'737'_752 (coe d_'43''45'isMonoid_2282 (coe v1)))
-- Algebra.Structures.IsNearring._.isMagma
d_isMagma_2686 :: T_IsNearring_2626 -> T_IsMagma_178
d_isMagma_2686 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe d_'43''45'isMonoid_2282 (coe d_isQuasiring_2644 (coe v0))))
-- Algebra.Structures.IsNearring._.+-isMonoid
d_'43''45'isMonoid_2688 :: T_IsNearring_2626 -> T_IsMonoid_712
d_'43''45'isMonoid_2688 v0
  = coe d_'43''45'isMonoid_2282 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.isSemigroup
d_isSemigroup_2690 :: T_IsNearring_2626 -> T_IsSemigroup_488
d_isSemigroup_2690 v0
  = coe
      d_isSemigroup_722
      (coe d_'43''45'isMonoid_2282 (coe d_isQuasiring_2644 (coe v0)))
-- Algebra.Structures.IsNearring._.isUnitalMagma
d_isUnitalMagma_2692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> T_IsUnitalMagma_666
d_isUnitalMagma_2692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_2692 v9
du_isUnitalMagma_2692 :: T_IsNearring_2626 -> T_IsUnitalMagma_666
du_isUnitalMagma_2692 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (coe du_isUnitalMagma_756 (coe d_'43''45'isMonoid_2282 (coe v1)))
-- Algebra.Structures.IsNearring._.distrib
d_distrib_2694 ::
  T_IsNearring_2626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2694 v0
  = coe d_distrib_2290 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.distribʳ
d_distrib'691'_2696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2626 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2696 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'691'_2696 v9
du_distrib'691'_2696 ::
  T_IsNearring_2626 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2696 v0
  = coe du_distrib'691'_2332 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.distribˡ
d_distrib'737'_2698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2626 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'737'_2698 v9
du_distrib'737'_2698 ::
  T_IsNearring_2626 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2698 v0
  = coe du_distrib'737'_2330 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.identityʳ
d_identity'691'_2700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> AgdaAny -> AgdaAny
d_identity'691'_2700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2700 v9
du_identity'691'_2700 :: T_IsNearring_2626 -> AgdaAny -> AgdaAny
du_identity'691'_2700 v0
  = coe du_identity'691'_2340 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.identityˡ
d_identity'737'_2702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> AgdaAny -> AgdaAny
d_identity'737'_2702 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2702 v9
du_identity'737'_2702 :: T_IsNearring_2626 -> AgdaAny -> AgdaAny
du_identity'737'_2702 v0
  = coe du_identity'737'_2338 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.isEquivalence
d_isEquivalence_2704 ::
  T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2704 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe d_'43''45'isMonoid_2282 (coe d_isQuasiring_2644 (coe v0)))))
-- Algebra.Structures.IsNearring._.isPartialEquivalence
d_isPartialEquivalence_2706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_2706 v9
du_isPartialEquivalence_2706 ::
  T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2706 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (let v2 = d_'43''45'isMonoid_2282 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe d_isEquivalence_186 (coe v4))))))
-- Algebra.Structures.IsNearring._.refl
d_refl_2708 :: T_IsNearring_2626 -> AgdaAny -> AgdaAny
d_refl_2708 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe d_'43''45'isMonoid_2282 (coe d_isQuasiring_2644 (coe v0))))))
-- Algebra.Structures.IsNearring._.reflexive
d_reflexive_2710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2626 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2710 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_2710 v9
du_reflexive_2710 ::
  T_IsNearring_2626 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2710 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (let v2 = d_'43''45'isMonoid_2282 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = d_isMagma_496 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe d_isEquivalence_186 (coe v4)) v5))))
-- Algebra.Structures.IsNearring._.setoid
d_setoid_2712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_2712 v9
du_setoid_2712 ::
  T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2712 v0
  = let v1 = d_isQuasiring_2644 (coe v0) in
    coe
      (let v2 = d_'43''45'isMonoid_2282 (coe v1) in
       coe
         (let v3 = d_isSemigroup_722 (coe v2) in
          coe (coe du_setoid_202 (coe d_isMagma_496 (coe v3)))))
-- Algebra.Structures.IsNearring._.sym
d_sym_2714 ::
  T_IsNearring_2626 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2714 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe d_'43''45'isMonoid_2282 (coe d_isQuasiring_2644 (coe v0))))))
-- Algebra.Structures.IsNearring._.trans
d_trans_2716 ::
  T_IsNearring_2626 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2716 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe d_'43''45'isMonoid_2282 (coe d_isQuasiring_2644 (coe v0))))))
-- Algebra.Structures.IsNearring._.zero
d_zero_2718 ::
  T_IsNearring_2626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2718 v0 = coe d_zero_2292 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.zeroʳ
d_zero'691'_2720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> AgdaAny -> AgdaAny
d_zero'691'_2720 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'691'_2720 v9
du_zero'691'_2720 :: T_IsNearring_2626 -> AgdaAny -> AgdaAny
du_zero'691'_2720 v0
  = coe du_zero'691'_2336 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring._.zeroˡ
d_zero'737'_2722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> AgdaAny -> AgdaAny
d_zero'737'_2722 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'737'_2722 v9
du_zero'737'_2722 :: T_IsNearring_2626 -> AgdaAny -> AgdaAny
du_zero'737'_2722 v0
  = coe du_zero'737'_2334 (coe d_isQuasiring_2644 (coe v0))
-- Algebra.Structures.IsNearring.+-inverseˡ
d_'43''45'inverse'737'_2724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> AgdaAny -> AgdaAny
d_'43''45'inverse'737'_2724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'43''45'inverse'737'_2724 v9
du_'43''45'inverse'737'_2724 ::
  T_IsNearring_2626 -> AgdaAny -> AgdaAny
du_'43''45'inverse'737'_2724 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_'43''45'inverse_2646 (coe v0))
-- Algebra.Structures.IsNearring.+-inverseʳ
d_'43''45'inverse'691'_2726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2626 -> AgdaAny -> AgdaAny
d_'43''45'inverse'691'_2726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'43''45'inverse'691'_2726 v9
du_'43''45'inverse'691'_2726 ::
  T_IsNearring_2626 -> AgdaAny -> AgdaAny
du_'43''45'inverse'691'_2726 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_'43''45'inverse_2646 (coe v0))
-- Algebra.Structures.IsRing
d_IsRing_2740 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsRing_2740
  = C_constructor_2876 T_IsAbelianGroup_1172
                       (AgdaAny ->
                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2762 ::
  T_IsRing_2740 -> T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2762 v0
  = case coe v0 of
      C_constructor_2876 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRing.*-cong
d_'42''45'cong_2764 ::
  T_IsRing_2740 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2764 v0
  = case coe v0 of
      C_constructor_2876 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRing.*-assoc
d_'42''45'assoc_2766 ::
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2766 v0
  = case coe v0 of
      C_constructor_2876 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRing.*-identity
d_'42''45'identity_2768 ::
  T_IsRing_2740 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2768 v0
  = case coe v0 of
      C_constructor_2876 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRing.distrib
d_distrib_2770 ::
  T_IsRing_2740 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2770 v0
  = case coe v0 of
      C_constructor_2876 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRing.isRingWithoutOne
d_isRingWithoutOne_2772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsRingWithoutOne_2368
d_isRingWithoutOne_2772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isRingWithoutOne_2772 v9
du_isRingWithoutOne_2772 ::
  T_IsRing_2740 -> T_IsRingWithoutOne_2368
du_isRingWithoutOne_2772 v0
  = coe
      C_constructor_2482 (coe d_'43''45'isAbelianGroup_2762 (coe v0))
      (coe d_'42''45'cong_2764 (coe v0))
      (coe d_'42''45'assoc_2766 (coe v0)) (coe d_distrib_2770 (coe v0))
-- Algebra.Structures.IsRing._._//_
d__'47''47'__2776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__2776 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du__'47''47'__2776 v4 v6
du__'47''47'__2776 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__2776 v0 v1 = coe du__'47''47'__1136 (coe v0) (coe v1)
-- Algebra.Structures.IsRing._.∙-congʳ
d_'8729''45'cong'691'_2778 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2778 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_'8729''45'cong'691'_2778 v4 v5 v6 v7 v9
du_'8729''45'cong'691'_2778 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2778 v0 v1 v2 v3 v4
  = let v5 = coe du_isRingWithoutOne_2772 (coe v4) in
    coe
      (let v6
             = coe
                 du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
                 (coe v5) in
       coe
         (let v7 = coe du_'42''45'isMagma_1324 (coe v6) in
          coe
            (let v8 = coe du_setoid_202 (coe v7) in
             coe
               (let v9 = d_'8729''45'cong_188 (coe v7) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v9)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v8))))))))
-- Algebra.Structures.IsRing._.∙-congˡ
d_'8729''45'cong'737'_2780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2780 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_'8729''45'cong'737'_2780 v4 v5 v6 v7 v9
du_'8729''45'cong'737'_2780 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2780 v0 v1 v2 v3 v4
  = let v5 = coe du_isRingWithoutOne_2772 (coe v4) in
    coe
      (let v6
             = coe
                 du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
                 (coe v5) in
       coe
         (let v7 = coe du_'42''45'isMagma_1324 (coe v6) in
          coe
            (let v8 = coe du_setoid_202 (coe v7) in
             coe
               (let v9 = d_'8729''45'cong_188 (coe v7) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v9)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v8))))))))
-- Algebra.Structures.IsRing._.*-isMagma
d_'42''45'isMagma_2782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsMagma_178
d_'42''45'isMagma_2782 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_'42''45'isMagma_2782 v4 v5 v6 v7 v9
du_'42''45'isMagma_2782 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_IsRing_2740 -> T_IsMagma_178
du_'42''45'isMagma_2782 v0 v1 v2 v3 v4
  = let v5 = coe du_isRingWithoutOne_2772 (coe v4) in
    coe
      (coe
         du_'42''45'isMagma_1324
         (coe
            du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v5)))
-- Algebra.Structures.IsRing._.*-isSemigroup
d_'42''45'isSemigroup_2784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsSemigroup_488
d_'42''45'isSemigroup_2784 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_'42''45'isSemigroup_2784 v4 v5 v6 v7 v9
du_'42''45'isSemigroup_2784 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2740 -> T_IsSemigroup_488
du_'42''45'isSemigroup_2784 v0 v1 v2 v3 v4
  = let v5 = coe du_isRingWithoutOne_2772 (coe v4) in
    coe
      (coe
         du_'42''45'isSemigroup_1326
         (coe
            du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v5)))
-- Algebra.Structures.IsRing._.assoc
d_assoc_2786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_assoc_2786 v9
du_assoc_2786 ::
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_2786 v0
  = coe
      d_assoc_498
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_1088
            (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0)))))
-- Algebra.Structures.IsRing._.comm
d_comm_2788 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2788 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_comm_2788 v9
du_comm_2788 :: T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_2788 v0
  = coe d_comm_1186 (coe d_'43''45'isAbelianGroup_2762 (coe v0))
-- Algebra.Structures.IsRing._.∙-cong
d_'8729''45'cong_2790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2790 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong_2790 v9
du_'8729''45'cong_2790 ::
  T_IsRing_2740 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_2790 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_1088
               (coe
                  d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0))))))
-- Algebra.Structures.IsRing._.∙-congʳ
d_'8729''45'cong'691'_2792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2792 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2792 v9
du_'8729''45'cong'691'_2792 ::
  T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2792 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe
         (let v3 = d_isGroup_1184 (coe v2) in
          coe
            (let v4 = d_isMonoid_1088 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (let v7 = coe du_setoid_202 (coe v6) in
                      coe
                        (let v8 = d_'8729''45'cong_188 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                    (coe v7)))))))))))
-- Algebra.Structures.IsRing._.∙-congˡ
d_'8729''45'cong'737'_2794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2794 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2794 v9
du_'8729''45'cong'737'_2794 ::
  T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2794 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe
         (let v3 = d_isGroup_1184 (coe v2) in
          coe
            (let v4 = d_isMonoid_1088 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (let v7 = coe du_setoid_202 (coe v6) in
                      coe
                        (let v8 = d_'8729''45'cong_188 (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                              (coe v8)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                    (coe v7)))))))))))
-- Algebra.Structures.IsRing._.identity
d_identity_2796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2740 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity_2796 v9
du_identity_2796 ::
  T_IsRing_2740 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_2796 v0
  = coe
      d_identity_724
      (coe
         d_isMonoid_1088
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0))))
-- Algebra.Structures.IsRing._.identityʳ
d_identity'691'_2798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
d_identity'691'_2798 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2798 v9
du_identity'691'_2798 :: T_IsRing_2740 -> AgdaAny -> AgdaAny
du_identity'691'_2798 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe
         (let v3 = d_isGroup_1184 (coe v2) in
          coe (coe du_identity'691'_754 (coe d_isMonoid_1088 (coe v3)))))
-- Algebra.Structures.IsRing._.identityˡ
d_identity'737'_2800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
d_identity'737'_2800 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2800 v9
du_identity'737'_2800 :: T_IsRing_2740 -> AgdaAny -> AgdaAny
du_identity'737'_2800 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe
         (let v3 = d_isGroup_1184 (coe v2) in
          coe (coe du_identity'737'_752 (coe d_isMonoid_1088 (coe v3)))))
-- Algebra.Structures.IsRing._.isCommutativeMagma
d_isCommutativeMagma_2802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_2802 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_2802 v9
du_isCommutativeMagma_2802 ::
  T_IsRing_2740 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_2802 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe
         (let v3 = coe du_isCommutativeMonoid_1244 (coe v2) in
          coe
            (coe
               du_isCommutativeMagma_606
               (coe du_isCommutativeSemigroup_814 (coe v3)))))
-- Algebra.Structures.IsRing._.isCommutativeMonoid
d_isCommutativeMonoid_2804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2804 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMonoid_2804 v9
du_isCommutativeMonoid_2804 ::
  T_IsRing_2740 -> T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2804 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (coe
         du_isCommutativeMonoid_1244
         (coe d_'43''45'isAbelianGroup_2386 (coe v1)))
-- Algebra.Structures.IsRing._.isCommutativeSemigroup
d_isCommutativeSemigroup_2806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2806 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              v9
  = du_isCommutativeSemigroup_2806 v9
du_isCommutativeSemigroup_2806 ::
  T_IsRing_2740 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2806 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe
         (coe
            du_isCommutativeSemigroup_814
            (coe du_isCommutativeMonoid_1244 (coe v2))))
-- Algebra.Structures.IsRing._.isGroup
d_isGroup_2808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsGroup_1074
d_isGroup_2808 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isGroup_2808 v9
du_isGroup_2808 :: T_IsRing_2740 -> T_IsGroup_1074
du_isGroup_2808 v0
  = coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0))
-- Algebra.Structures.IsRing._.isInvertibleMagma
d_isInvertibleMagma_2810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsInvertibleMagma_958
d_isInvertibleMagma_2810 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isInvertibleMagma_2810 v9
du_isInvertibleMagma_2810 ::
  T_IsRing_2740 -> T_IsInvertibleMagma_958
du_isInvertibleMagma_2810 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe (coe du_isInvertibleMagma_1160 (coe d_isGroup_1184 (coe v2))))
-- Algebra.Structures.IsRing._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2740 -> T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_2812 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_isInvertibleUnitalMagma_2812 v9
du_isInvertibleUnitalMagma_2812 ::
  T_IsRing_2740 -> T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_2812 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe
         (coe
            du_isInvertibleUnitalMagma_1162 (coe d_isGroup_1184 (coe v2))))
-- Algebra.Structures.IsRing._.isMagma
d_isMagma_2814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsMagma_178
d_isMagma_2814 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isMagma_2814 v9
du_isMagma_2814 :: T_IsRing_2740 -> T_IsMagma_178
du_isMagma_2814 v0
  = coe
      d_isMagma_496
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_1088
            (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0)))))
-- Algebra.Structures.IsRing._.isMonoid
d_isMonoid_2816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsMonoid_712
d_isMonoid_2816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isMonoid_2816 v9
du_isMonoid_2816 :: T_IsRing_2740 -> T_IsMonoid_712
du_isMonoid_2816 v0
  = coe
      d_isMonoid_1088
      (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0)))
-- Algebra.Structures.IsRing._.isSemigroup
d_isSemigroup_2818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsSemigroup_488
d_isSemigroup_2818 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isSemigroup_2818 v9
du_isSemigroup_2818 :: T_IsRing_2740 -> T_IsSemigroup_488
du_isSemigroup_2818 v0
  = coe
      d_isSemigroup_722
      (coe
         d_isMonoid_1088
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0))))
-- Algebra.Structures.IsRing._.isUnitalMagma
d_isUnitalMagma_2820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsUnitalMagma_666
d_isUnitalMagma_2820 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_2820 v9
du_isUnitalMagma_2820 :: T_IsRing_2740 -> T_IsUnitalMagma_666
du_isUnitalMagma_2820 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe
         (let v3 = d_isGroup_1184 (coe v2) in
          coe (coe du_isUnitalMagma_756 (coe d_isMonoid_1088 (coe v3)))))
-- Algebra.Structures.IsRing._.⁻¹-cong
d_'8315''185''45'cong_2822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_2822 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8315''185''45'cong_2822 v9
du_'8315''185''45'cong_2822 ::
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'cong_2822 v0
  = coe
      d_'8315''185''45'cong_1092
      (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0)))
-- Algebra.Structures.IsRing._.inverse
d_inverse_2824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2740 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse_2824 v9
du_inverse_2824 ::
  T_IsRing_2740 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_2824 v0
  = coe
      d_inverse_1090
      (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0)))
-- Algebra.Structures.IsRing._.inverseʳ
d_inverse'691'_2826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
d_inverse'691'_2826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'691'_2826 v9
du_inverse'691'_2826 :: T_IsRing_2740 -> AgdaAny -> AgdaAny
du_inverse'691'_2826 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe (coe du_inverse'691'_1146 (coe d_isGroup_1184 (coe v2))))
-- Algebra.Structures.IsRing._.inverseˡ
d_inverse'737'_2828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
d_inverse'737'_2828 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'737'_2828 v9
du_inverse'737'_2828 :: T_IsRing_2740 -> AgdaAny -> AgdaAny
du_inverse'737'_2828 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe (coe du_inverse'737'_1144 (coe d_isGroup_1184 (coe v2))))
-- Algebra.Structures.IsRing._.distribʳ
d_distrib'691'_2830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'691'_2830 v9
du_distrib'691'_2830 ::
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2830 v0
  = coe du_distrib'691'_2462 (coe du_isRingWithoutOne_2772 (coe v0))
-- Algebra.Structures.IsRing._.distribˡ
d_distrib'737'_2832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'737'_2832 v9
du_distrib'737'_2832 ::
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2832 v0
  = coe du_distrib'737'_2460 (coe du_isRingWithoutOne_2772 (coe v0))
-- Algebra.Structures.IsRing._.isEquivalence
d_isEquivalence_2834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2834 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_2834 v9
du_isEquivalence_2834 ::
  T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2834 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_1088
               (coe
                  d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0))))))
-- Algebra.Structures.IsRing._.isNearSemiring
d_isNearSemiring_2836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsNearSemiring_1260
d_isNearSemiring_2836 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isNearSemiring_2836 v4 v5 v6 v7 v9
du_isNearSemiring_2836 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2740 -> T_IsNearSemiring_1260
du_isNearSemiring_2836 v0 v1 v2 v3 v4
  = coe
      du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_isRingWithoutOne_2772 (coe v4))
-- Algebra.Structures.IsRing._.isPartialEquivalence
d_isPartialEquivalence_2838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2838 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_2838 v9
du_isPartialEquivalence_2838 ::
  T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2838 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe
         (let v3 = d_isGroup_1184 (coe v2) in
          coe
            (let v4 = d_isMonoid_1088 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                        (coe d_isEquivalence_186 (coe v6))))))))
-- Algebra.Structures.IsRing._.refl
d_refl_2840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
d_refl_2840 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_refl_2840 v9
du_refl_2840 :: T_IsRing_2740 -> AgdaAny -> AgdaAny
du_refl_2840 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0)))))))
-- Algebra.Structures.IsRing._.reflexive
d_reflexive_2842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2842 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_2842 v9
du_reflexive_2842 ::
  T_IsRing_2740 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2842 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe
         (let v3 = d_isGroup_1184 (coe v2) in
          coe
            (let v4 = d_isMonoid_1088 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = d_isMagma_496 (coe v5) in
                   coe
                     (\ v7 v8 v9 ->
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                          (coe d_isEquivalence_186 (coe v6)) v7))))))
-- Algebra.Structures.IsRing._.setoid
d_setoid_2844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2844 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_2844 v9
du_setoid_2844 ::
  T_IsRing_2740 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2844 v0
  = let v1 = coe du_isRingWithoutOne_2772 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2386 (coe v1) in
       coe
         (let v3 = d_isGroup_1184 (coe v2) in
          coe
            (let v4 = d_isMonoid_1088 (coe v3) in
             coe
               (let v5 = d_isSemigroup_722 (coe v4) in
                coe (coe du_setoid_202 (coe d_isMagma_496 (coe v5)))))))
-- Algebra.Structures.IsRing._.sym
d_sym_2846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2846 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_2846 v9
du_sym_2846 ::
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2846 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0)))))))
-- Algebra.Structures.IsRing._.trans
d_trans_2848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2848 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_2848 v9
du_trans_2848 ::
  T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2848 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v0)))))))
-- Algebra.Structures.IsRing._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_2850 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'691''45''8315''185'_2850 v4 v6 v7 v9
du_unique'691''45''8315''185'_2850 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_2850 v0 v1 v2 v3
  = let v4 = coe du_isRingWithoutOne_2772 (coe v3) in
    coe
      (let v5 = d_'43''45'isAbelianGroup_2386 (coe v4) in
       coe
         (coe
            du_unique'691''45''8315''185'_1158 (coe v0) (coe v2) (coe v1)
            (coe d_isGroup_1184 (coe v5))))
-- Algebra.Structures.IsRing._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_2852 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'737''45''8315''185'_2852 v4 v6 v7 v9
du_unique'737''45''8315''185'_2852 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRing_2740 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_2852 v0 v1 v2 v3
  = let v4 = coe du_isRingWithoutOne_2772 (coe v3) in
    coe
      (let v5 = d_'43''45'isAbelianGroup_2386 (coe v4) in
       coe
         (coe
            du_unique'737''45''8315''185'_1152 (coe v0) (coe v2) (coe v1)
            (coe d_isGroup_1184 (coe v5))))
-- Algebra.Structures.IsRing._.zero
d_zero_2854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2740 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2854 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero_2854 v4 v5 v6 v7 v9
du_zero_2854 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2740 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_2854 v0 v1 v2 v3 v4
  = coe
      du_zero_2468 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_isRingWithoutOne_2772 (coe v4))
-- Algebra.Structures.IsRing._.zeroʳ
d_zero'691'_2856 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
d_zero'691'_2856 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'691'_2856 v4 v5 v6 v7 v9
du_zero'691'_2856 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
du_zero'691'_2856 v0 v1 v2 v3 v4
  = coe
      du_zero'691'_2466 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_isRingWithoutOne_2772 (coe v4))
-- Algebra.Structures.IsRing._.zeroˡ
d_zero'737'_2858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
d_zero'737'_2858 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'737'_2858 v4 v5 v6 v7 v9
du_zero'737'_2858 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
du_zero'737'_2858 v0 v1 v2 v3 v4
  = coe
      du_zero'737'_2464 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_isRingWithoutOne_2772 (coe v4))
-- Algebra.Structures.IsRing.*-isMonoid
d_'42''45'isMonoid_2860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsMonoid_712
d_'42''45'isMonoid_2860 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_'42''45'isMonoid_2860 v4 v5 v6 v7 v9
du_'42''45'isMonoid_2860 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_IsRing_2740 -> T_IsMonoid_712
du_'42''45'isMonoid_2860 v0 v1 v2 v3 v4
  = coe
      C_constructor_758
      (coe
         du_'42''45'isSemigroup_1326
         (coe
            du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe du_isRingWithoutOne_2772 (coe v4))))
      (coe d_'42''45'identity_2768 (coe v4))
-- Algebra.Structures.IsRing._.identityʳ
d_identity'691'_2864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
d_identity'691'_2864 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_identity'691'_2864 v4 v5 v6 v7 v9
du_identity'691'_2864 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
du_identity'691'_2864 v0 v1 v2 v3 v4
  = coe
      du_identity'691'_754
      (coe
         du_'42''45'isMonoid_2860 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Algebra.Structures.IsRing._.identityˡ
d_identity'737'_2866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
d_identity'737'_2866 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_identity'737'_2866 v4 v5 v6 v7 v9
du_identity'737'_2866 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2740 -> AgdaAny -> AgdaAny
du_identity'737'_2866 v0 v1 v2 v3 v4
  = coe
      du_identity'737'_752
      (coe
         du_'42''45'isMonoid_2860 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Algebra.Structures.IsRing.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2740 -> T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2868 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                         ~v6 ~v7 ~v8 v9
  = du_isSemiringWithoutAnnihilatingZero_2868 v9
du_isSemiringWithoutAnnihilatingZero_2868 ::
  T_IsRing_2740 -> T_IsSemiringWithoutAnnihilatingZero_1536
du_isSemiringWithoutAnnihilatingZero_2868 v0
  = coe
      C_constructor_1630
      (coe
         du_isCommutativeMonoid_1244
         (coe d_'43''45'isAbelianGroup_2762 (coe v0)))
      (coe d_'42''45'cong_2764 (coe v0))
      (coe d_'42''45'assoc_2766 (coe v0))
      (coe d_'42''45'identity_2768 (coe v0))
      (coe d_distrib_2770 (coe v0))
-- Algebra.Structures.IsRing.isSemiring
d_isSemiring_2870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsSemiring_1640
d_isSemiring_2870 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isSemiring_2870 v4 v5 v6 v7 v9
du_isSemiring_2870 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2740 -> T_IsSemiring_1640
du_isSemiring_2870 v0 v1 v2 v3 v4
  = coe
      C_constructor_1740
      (coe du_isSemiringWithoutAnnihilatingZero_2868 (coe v4))
      (coe
         du_zero_2468 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe du_isRingWithoutOne_2772 (coe v4)))
-- Algebra.Structures.IsRing._.isSemiringWithoutOne
d_isSemiringWithoutOne_2874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2740 -> T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2874 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isSemiringWithoutOne_2874 v4 v5 v6 v7 v9
du_isSemiringWithoutOne_2874 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2740 -> T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_2874 v0 v1 v2 v3 v4
  = coe
      du_isSemiringWithoutOne_1730
      (coe
         du_isSemiring_2870 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Structures.IsCommutativeRing
d_IsCommutativeRing_2888 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsCommutativeRing_2888
  = C_constructor_3030 T_IsRing_2740 (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeRing.isRing
d_isRing_2904 :: T_IsCommutativeRing_2888 -> T_IsRing_2740
d_isRing_2904 v0
  = case coe v0 of
      C_constructor_3030 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeRing.*-comm
d_'42''45'comm_2906 ::
  T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_2906 v0
  = case coe v0 of
      C_constructor_3030 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeRing._._//_
d__'47''47'__2910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__2910 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du__'47''47'__2910 v4 v6
du__'47''47'__2910 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__2910 v0 v1 = coe du__'47''47'__1136 (coe v0) (coe v1)
-- Algebra.Structures.IsCommutativeRing._.*-assoc
d_'42''45'assoc_2912 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2912 v0
  = coe d_'42''45'assoc_2766 (coe d_isRing_2904 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.*-cong
d_'42''45'cong_2914 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2914 v0
  = coe d_'42''45'cong_2764 (coe d_isRing_2904 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_2916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2916 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_'8729''45'cong'691'_2916 v4 v5 v6 v7 v9
du_'8729''45'cong'691'_2916 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2916 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2904 (coe v4) in
    coe
      (let v6 = coe du_isRingWithoutOne_2772 (coe v5) in
       coe
         (let v7
                = coe
                    du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v6) in
          coe
            (let v8 = coe du_'42''45'isMagma_1324 (coe v7) in
             coe
               (let v9 = coe du_setoid_202 (coe v8) in
                coe
                  (let v10 = d_'8729''45'cong_188 (coe v8) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v10)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v9)))))))))
-- Algebra.Structures.IsCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_2918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2918 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_'8729''45'cong'737'_2918 v4 v5 v6 v7 v9
du_'8729''45'cong'737'_2918 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2918 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2904 (coe v4) in
    coe
      (let v6 = coe du_isRingWithoutOne_2772 (coe v5) in
       coe
         (let v7
                = coe
                    du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v6) in
          coe
            (let v8 = coe du_'42''45'isMagma_1324 (coe v7) in
             coe
               (let v9 = coe du_setoid_202 (coe v8) in
                coe
                  (let v10 = d_'8729''45'cong_188 (coe v8) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v10)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v9)))))))))
-- Algebra.Structures.IsCommutativeRing._.*-identity
d_'42''45'identity_2920 ::
  T_IsCommutativeRing_2888 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2920 v0
  = coe d_'42''45'identity_2768 (coe d_isRing_2904 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.identityʳ
d_identity'691'_2922 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
d_identity'691'_2922 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_identity'691'_2922 v4 v5 v6 v7 v9
du_identity'691'_2922 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
du_identity'691'_2922 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2904 (coe v4) in
    coe
      (coe
         du_identity'691'_754
         (coe
            du_'42''45'isMonoid_2860 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v5)))
-- Algebra.Structures.IsCommutativeRing._.identityˡ
d_identity'737'_2924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
d_identity'737'_2924 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_identity'737'_2924 v4 v5 v6 v7 v9
du_identity'737'_2924 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
du_identity'737'_2924 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2904 (coe v4) in
    coe
      (coe
         du_identity'737'_752
         (coe
            du_'42''45'isMonoid_2860 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v5)))
-- Algebra.Structures.IsCommutativeRing._.*-isMagma
d_'42''45'isMagma_2926 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2888 -> T_IsMagma_178
d_'42''45'isMagma_2926 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_'42''45'isMagma_2926 v4 v5 v6 v7 v9
du_'42''45'isMagma_2926 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsMagma_178
du_'42''45'isMagma_2926 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2904 (coe v4) in
    coe
      (let v6 = coe du_isRingWithoutOne_2772 (coe v5) in
       coe
         (coe
            du_'42''45'isMagma_1324
            (coe
               du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
               (coe v6))))
-- Algebra.Structures.IsCommutativeRing._.*-isMonoid
d_'42''45'isMonoid_2928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2888 -> T_IsMonoid_712
d_'42''45'isMonoid_2928 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_'42''45'isMonoid_2928 v4 v5 v6 v7 v9
du_'42''45'isMonoid_2928 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsMonoid_712
du_'42''45'isMonoid_2928 v0 v1 v2 v3 v4
  = coe
      du_'42''45'isMonoid_2860 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe d_isRing_2904 (coe v4))
-- Algebra.Structures.IsCommutativeRing._.*-isSemigroup
d_'42''45'isSemigroup_2930 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2888 -> T_IsSemigroup_488
d_'42''45'isSemigroup_2930 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_'42''45'isSemigroup_2930 v4 v5 v6 v7 v9
du_'42''45'isSemigroup_2930 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsSemigroup_488
du_'42''45'isSemigroup_2930 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2904 (coe v4) in
    coe
      (let v6 = coe du_isRingWithoutOne_2772 (coe v5) in
       coe
         (coe
            du_'42''45'isSemigroup_1326
            (coe
               du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
               (coe v6))))
-- Algebra.Structures.IsCommutativeRing._.assoc
d_assoc_2932 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2932 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_assoc_2932 v9
du_assoc_2932 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_2932 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         d_assoc_498
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_1088
               (coe
                  d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1))))))
-- Algebra.Structures.IsCommutativeRing._.comm
d_comm_2934 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2934 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_comm_2934 v9
du_comm_2934 ::
  T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_2934 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe (coe d_comm_1186 (coe d_'43''45'isAbelianGroup_2762 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.∙-cong
d_'8729''45'cong_2936 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2936 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong_2936 v9
du_'8729''45'cong_2936 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_2936 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         d_'8729''45'cong_188
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1)))))))
-- Algebra.Structures.IsCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_2938 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2938 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2938 v9
du_'8729''45'cong'691'_2938 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2938 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe
            (let v4 = d_isGroup_1184 (coe v3) in
             coe
               (let v5 = d_isMonoid_1088 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (let v8 = coe du_setoid_202 (coe v7) in
                         coe
                           (let v9 = d_'8729''45'cong_188 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                       (coe v8))))))))))))
-- Algebra.Structures.IsCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_2940 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2940 v9
du_'8729''45'cong'737'_2940 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2940 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe
            (let v4 = d_isGroup_1184 (coe v3) in
             coe
               (let v5 = d_isMonoid_1088 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (let v8 = coe du_setoid_202 (coe v7) in
                         coe
                           (let v9 = d_'8729''45'cong_188 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                       (coe v8))))))))))))
-- Algebra.Structures.IsCommutativeRing._.identity
d_identity_2942 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2942 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity_2942 v9
du_identity_2942 ::
  T_IsCommutativeRing_2888 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_2942 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         d_identity_724
         (coe
            d_isMonoid_1088
            (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1)))))
-- Algebra.Structures.IsCommutativeRing._.identityʳ
d_identity'691'_2944 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
d_identity'691'_2944 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2944 v9
du_identity'691'_2944 ::
  T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
du_identity'691'_2944 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe
            (let v4 = d_isGroup_1184 (coe v3) in
             coe (coe du_identity'691'_754 (coe d_isMonoid_1088 (coe v4))))))
-- Algebra.Structures.IsCommutativeRing._.identityˡ
d_identity'737'_2946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
d_identity'737'_2946 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2946 v9
du_identity'737'_2946 ::
  T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
du_identity'737'_2946 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe
            (let v4 = d_isGroup_1184 (coe v3) in
             coe (coe du_identity'737'_752 (coe d_isMonoid_1088 (coe v4))))))
-- Algebra.Structures.IsCommutativeRing._.+-isAbelianGroup
d_'43''45'isAbelianGroup_2948 ::
  T_IsCommutativeRing_2888 -> T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2948 v0
  = coe d_'43''45'isAbelianGroup_2762 (coe d_isRing_2904 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_2950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_2950 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_2950 v9
du_isCommutativeMagma_2950 ::
  T_IsCommutativeRing_2888 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_2950 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe
            (let v4 = coe du_isCommutativeMonoid_1244 (coe v3) in
             coe
               (coe
                  du_isCommutativeMagma_606
                  (coe du_isCommutativeSemigroup_814 (coe v4))))))
-- Algebra.Structures.IsCommutativeRing._.isCommutativeMonoid
d_isCommutativeMonoid_2952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2952 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMonoid_2952 v9
du_isCommutativeMonoid_2952 ::
  T_IsCommutativeRing_2888 -> T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2952 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (coe
            du_isCommutativeMonoid_1244
            (coe d_'43''45'isAbelianGroup_2386 (coe v2))))
-- Algebra.Structures.IsCommutativeRing._.isCommutativeSemigroup
d_isCommutativeSemigroup_2954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              v9
  = du_isCommutativeSemigroup_2954 v9
du_isCommutativeSemigroup_2954 ::
  T_IsCommutativeRing_2888 -> T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2954 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe
            (coe
               du_isCommutativeSemigroup_814
               (coe du_isCommutativeMonoid_1244 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.isGroup
d_isGroup_2956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2888 -> T_IsGroup_1074
d_isGroup_2956 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isGroup_2956 v9
du_isGroup_2956 :: T_IsCommutativeRing_2888 -> T_IsGroup_1074
du_isGroup_2956 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.isInvertibleMagma
d_isInvertibleMagma_2958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsInvertibleMagma_958
d_isInvertibleMagma_2958 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isInvertibleMagma_2958 v9
du_isInvertibleMagma_2958 ::
  T_IsCommutativeRing_2888 -> T_IsInvertibleMagma_958
du_isInvertibleMagma_2958 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe (coe du_isInvertibleMagma_1160 (coe d_isGroup_1184 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 -> T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_2960 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_isInvertibleUnitalMagma_2960 v9
du_isInvertibleUnitalMagma_2960 ::
  T_IsCommutativeRing_2888 -> T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_2960 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe
            (coe
               du_isInvertibleUnitalMagma_1162 (coe d_isGroup_1184 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.isMagma
d_isMagma_2962 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2888 -> T_IsMagma_178
d_isMagma_2962 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isMagma_2962 v9
du_isMagma_2962 :: T_IsCommutativeRing_2888 -> T_IsMagma_178
du_isMagma_2962 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         d_isMagma_496
         (coe
            d_isSemigroup_722
            (coe
               d_isMonoid_1088
               (coe
                  d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1))))))
-- Algebra.Structures.IsCommutativeRing._.isMonoid
d_isMonoid_2964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2888 -> T_IsMonoid_712
d_isMonoid_2964 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isMonoid_2964 v9
du_isMonoid_2964 :: T_IsCommutativeRing_2888 -> T_IsMonoid_712
du_isMonoid_2964 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         d_isMonoid_1088
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1))))
-- Algebra.Structures.IsCommutativeRing._.isSemigroup
d_isSemigroup_2966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2888 -> T_IsSemigroup_488
d_isSemigroup_2966 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isSemigroup_2966 v9
du_isSemigroup_2966 ::
  T_IsCommutativeRing_2888 -> T_IsSemigroup_488
du_isSemigroup_2966 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         d_isSemigroup_722
         (coe
            d_isMonoid_1088
            (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1)))))
-- Algebra.Structures.IsCommutativeRing._.isUnitalMagma
d_isUnitalMagma_2968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsUnitalMagma_666
d_isUnitalMagma_2968 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_2968 v9
du_isUnitalMagma_2968 ::
  T_IsCommutativeRing_2888 -> T_IsUnitalMagma_666
du_isUnitalMagma_2968 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe
            (let v4 = d_isGroup_1184 (coe v3) in
             coe (coe du_isUnitalMagma_756 (coe d_isMonoid_1088 (coe v4))))))
-- Algebra.Structures.IsCommutativeRing._.⁻¹-cong
d_'8315''185''45'cong_2970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_2970 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8315''185''45'cong_2970 v9
du_'8315''185''45'cong_2970 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'cong_2970 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         d_'8315''185''45'cong_1092
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1))))
-- Algebra.Structures.IsCommutativeRing._.inverse
d_inverse_2972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2972 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse_2972 v9
du_inverse_2972 ::
  T_IsCommutativeRing_2888 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_2972 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         d_inverse_1090
         (coe d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1))))
-- Algebra.Structures.IsCommutativeRing._.inverseʳ
d_inverse'691'_2974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
d_inverse'691'_2974 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'691'_2974 v9
du_inverse'691'_2974 ::
  T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
du_inverse'691'_2974 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe (coe du_inverse'691'_1146 (coe d_isGroup_1184 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.inverseˡ
d_inverse'737'_2976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
d_inverse'737'_2976 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'737'_2976 v9
du_inverse'737'_2976 ::
  T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
du_inverse'737'_2976 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe (coe du_inverse'737'_1144 (coe d_isGroup_1184 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.distrib
d_distrib_2978 ::
  T_IsCommutativeRing_2888 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2978 v0 = coe d_distrib_2770 (coe d_isRing_2904 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.distribʳ
d_distrib'691'_2980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2980 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'691'_2980 v9
du_distrib'691'_2980 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2980 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe du_distrib'691'_2462 (coe du_isRingWithoutOne_2772 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.distribˡ
d_distrib'737'_2982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2982 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'737'_2982 v9
du_distrib'737'_2982 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2982 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe du_distrib'737'_2460 (coe du_isRingWithoutOne_2772 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.isEquivalence
d_isEquivalence_2984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2984 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_2984 v9
du_isEquivalence_2984 ::
  T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2984 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_496
            (coe
               d_isSemigroup_722
               (coe
                  d_isMonoid_1088
                  (coe
                     d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1)))))))
-- Algebra.Structures.IsCommutativeRing._.isNearSemiring
d_isNearSemiring_2986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsNearSemiring_1260
d_isNearSemiring_2986 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isNearSemiring_2986 v4 v5 v6 v7 v9
du_isNearSemiring_2986 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsNearSemiring_1260
du_isNearSemiring_2986 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2904 (coe v4) in
    coe
      (coe
         du_isNearSemiring_2470 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe du_isRingWithoutOne_2772 (coe v5)))
-- Algebra.Structures.IsCommutativeRing._.isPartialEquivalence
d_isPartialEquivalence_2988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2988 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_2988 v9
du_isPartialEquivalence_2988 ::
  T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2988 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe
            (let v4 = d_isGroup_1184 (coe v3) in
             coe
               (let v5 = d_isMonoid_1088 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                           (coe d_isEquivalence_186 (coe v7)))))))))
-- Algebra.Structures.IsCommutativeRing._.isRingWithoutOne
d_isRingWithoutOne_2990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsRingWithoutOne_2368
d_isRingWithoutOne_2990 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isRingWithoutOne_2990 v9
du_isRingWithoutOne_2990 ::
  T_IsCommutativeRing_2888 -> T_IsRingWithoutOne_2368
du_isRingWithoutOne_2990 v0
  = coe du_isRingWithoutOne_2772 (coe d_isRing_2904 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.isSemiring
d_isSemiring_2992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2888 -> T_IsSemiring_1640
d_isSemiring_2992 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isSemiring_2992 v4 v5 v6 v7 v9
du_isSemiring_2992 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsSemiring_1640
du_isSemiring_2992 v0 v1 v2 v3 v4
  = coe
      du_isSemiring_2870 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe d_isRing_2904 (coe v4))
-- Algebra.Structures.IsCommutativeRing._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2994 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                         ~v6 ~v7 ~v8 v9
  = du_isSemiringWithoutAnnihilatingZero_2994 v9
du_isSemiringWithoutAnnihilatingZero_2994 ::
  T_IsCommutativeRing_2888 ->
  T_IsSemiringWithoutAnnihilatingZero_1536
du_isSemiringWithoutAnnihilatingZero_2994 v0
  = coe
      du_isSemiringWithoutAnnihilatingZero_2868
      (coe d_isRing_2904 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.isSemiringWithoutOne
d_isSemiringWithoutOne_2996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2996 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isSemiringWithoutOne_2996 v4 v5 v6 v7 v9
du_isSemiringWithoutOne_2996 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_2996 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2904 (coe v4) in
    coe
      (coe
         du_isSemiringWithoutOne_1730
         (coe
            du_isSemiring_2870 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)))
-- Algebra.Structures.IsCommutativeRing._.refl
d_refl_2998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
d_refl_2998 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_refl_2998 v9
du_refl_2998 :: T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
du_refl_2998 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            d_isEquivalence_186
            (coe
               d_isMagma_496
               (coe
                  d_isSemigroup_722
                  (coe
                     d_isMonoid_1088
                     (coe
                        d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1))))))))
-- Algebra.Structures.IsCommutativeRing._.reflexive
d_reflexive_3000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3000 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_3000 v9
du_reflexive_3000 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3000 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe
            (let v4 = d_isGroup_1184 (coe v3) in
             coe
               (let v5 = d_isMonoid_1088 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = d_isMagma_496 (coe v6) in
                      coe
                        (\ v8 v9 v10 ->
                           coe
                             MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                             (coe d_isEquivalence_186 (coe v7)) v8)))))))
-- Algebra.Structures.IsCommutativeRing._.setoid
d_setoid_3002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_3002 v9
du_setoid_3002 ::
  T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3002 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2772 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2386 (coe v2) in
          coe
            (let v4 = d_isGroup_1184 (coe v3) in
             coe
               (let v5 = d_isMonoid_1088 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_722 (coe v5) in
                   coe (coe du_setoid_202 (coe d_isMagma_496 (coe v6))))))))
-- Algebra.Structures.IsCommutativeRing._.sym
d_sym_3004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3004 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_3004 v9
du_sym_3004 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_3004 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            d_isEquivalence_186
            (coe
               d_isMagma_496
               (coe
                  d_isSemigroup_722
                  (coe
                     d_isMonoid_1088
                     (coe
                        d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1))))))))
-- Algebra.Structures.IsCommutativeRing._.trans
d_trans_3006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3006 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_3006 v9
du_trans_3006 ::
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_3006 v0
  = let v1 = d_isRing_2904 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe
            d_isEquivalence_186
            (coe
               d_isMagma_496
               (coe
                  d_isSemigroup_722
                  (coe
                     d_isMonoid_1088
                     (coe
                        d_isGroup_1184 (coe d_'43''45'isAbelianGroup_2762 (coe v1))))))))
-- Algebra.Structures.IsCommutativeRing._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_3008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_3008 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'691''45''8315''185'_3008 v4 v6 v7 v9
du_unique'691''45''8315''185'_3008 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_3008 v0 v1 v2 v3
  = let v4 = d_isRing_2904 (coe v3) in
    coe
      (let v5 = coe du_isRingWithoutOne_2772 (coe v4) in
       coe
         (let v6 = d_'43''45'isAbelianGroup_2386 (coe v5) in
          coe
            (coe
               du_unique'691''45''8315''185'_1158 (coe v0) (coe v2) (coe v1)
               (coe d_isGroup_1184 (coe v6)))))
-- Algebra.Structures.IsCommutativeRing._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_3010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_3010 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'737''45''8315''185'_3010 v4 v6 v7 v9
du_unique'737''45''8315''185'_3010 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_3010 v0 v1 v2 v3
  = let v4 = d_isRing_2904 (coe v3) in
    coe
      (let v5 = coe du_isRingWithoutOne_2772 (coe v4) in
       coe
         (let v6 = d_'43''45'isAbelianGroup_2386 (coe v5) in
          coe
            (coe
               du_unique'737''45''8315''185'_1152 (coe v0) (coe v2) (coe v1)
               (coe d_isGroup_1184 (coe v6)))))
-- Algebra.Structures.IsCommutativeRing._.zero
d_zero_3012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_3012 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero_3012 v4 v5 v6 v7 v9
du_zero_3012 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeRing_2888 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_3012 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2904 (coe v4) in
    coe
      (coe
         du_zero_2468 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe du_isRingWithoutOne_2772 (coe v5)))
-- Algebra.Structures.IsCommutativeRing._.zeroʳ
d_zero'691'_3014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
d_zero'691'_3014 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'691'_3014 v4 v5 v6 v7 v9
du_zero'691'_3014 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
du_zero'691'_3014 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2904 (coe v4) in
    coe
      (coe
         du_zero'691'_2466 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe du_isRingWithoutOne_2772 (coe v5)))
-- Algebra.Structures.IsCommutativeRing._.zeroˡ
d_zero'737'_3016 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
d_zero'737'_3016 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'737'_3016 v4 v5 v6 v7 v9
du_zero'737'_3016 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> AgdaAny -> AgdaAny
du_zero'737'_3016 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2904 (coe v4) in
    coe
      (coe
         du_zero'737'_2464 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe du_isRingWithoutOne_2772 (coe v5)))
-- Algebra.Structures.IsCommutativeRing.isCommutativeSemiring
d_isCommutativeSemiring_3018 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_3018 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isCommutativeSemiring_3018 v4 v5 v6 v7 v9
du_isCommutativeSemiring_3018 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsCommutativeSemiring_1750
du_isCommutativeSemiring_3018 v0 v1 v2 v3 v4
  = coe
      C_constructor_1862
      (coe
         du_isSemiring_2870 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe d_isRing_2904 (coe v4)))
      (coe d_'42''45'comm_2906 (coe v4))
-- Algebra.Structures.IsCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_3022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsCommutativeMagma_214
d_isCommutativeMagma_3022 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isCommutativeMagma_3022 v4 v5 v6 v7 v9
du_isCommutativeMagma_3022 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsCommutativeMagma_214
du_isCommutativeMagma_3022 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_isCommutativeSemiring_3018 (coe v0) (coe v1) (coe v2) (coe v3)
              (coe v4) in
    coe
      (let v6 = coe du_isCommutativeSemiringWithoutOne_1852 (coe v5) in
       coe
         (coe
            du_isCommutativeMagma_606
            (coe du_'42''45'isCommutativeSemigroup_1520 (coe v6))))
-- Algebra.Structures.IsCommutativeRing._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_3024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_3024 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8
                                   v9
  = du_'42''45'isCommutativeMonoid_3024 v4 v5 v6 v7 v9
du_'42''45'isCommutativeMonoid_3024 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsCommutativeMonoid_764
du_'42''45'isCommutativeMonoid_3024 v0 v1 v2 v3 v4
  = coe
      du_'42''45'isCommutativeMonoid_1860
      (coe
         du_isCommutativeSemiring_3018 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Algebra.Structures.IsCommutativeRing._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_3026 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_3026 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                      ~v8 v9
  = du_'42''45'isCommutativeSemigroup_3026 v4 v5 v6 v7 v9
du_'42''45'isCommutativeSemigroup_3026 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2888 -> T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_3026 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_isCommutativeSemiring_3018 (coe v0) (coe v1) (coe v2) (coe v3)
              (coe v4) in
    coe
      (coe
         du_'42''45'isCommutativeSemigroup_1520
         (coe du_isCommutativeSemiringWithoutOne_1852 (coe v5)))
-- Algebra.Structures.IsCommutativeRing._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_3028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2888 -> T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_3028 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                       ~v8 v9
  = du_isCommutativeSemiringWithoutOne_3028 v4 v5 v6 v7 v9
du_isCommutativeSemiringWithoutOne_3028 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeRing_2888 -> T_IsCommutativeSemiringWithoutOne_1438
du_isCommutativeSemiringWithoutOne_3028 v0 v1 v2 v3 v4
  = coe
      du_isCommutativeSemiringWithoutOne_1852
      (coe
         du_isCommutativeSemiring_3018 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Algebra.Structures.IsQuasigroup
d_IsQuasigroup_3038 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsQuasigroup_3038
  = C_constructor_3112 T_IsMagma_178
                       (AgdaAny ->
                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny ->
                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsQuasigroup.isMagma
d_isMagma_3056 :: T_IsQuasigroup_3038 -> T_IsMagma_178
d_isMagma_3056 v0
  = case coe v0 of
      C_constructor_3112 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasigroup.\\-cong
d_'92''92''45'cong_3058 ::
  T_IsQuasigroup_3038 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_3058 v0
  = case coe v0 of
      C_constructor_3112 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasigroup.//-cong
d_'47''47''45'cong_3060 ::
  T_IsQuasigroup_3038 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_3060 v0
  = case coe v0 of
      C_constructor_3112 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasigroup.leftDivides
d_leftDivides_3062 ::
  T_IsQuasigroup_3038 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_3062 v0
  = case coe v0 of
      C_constructor_3112 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasigroup.rightDivides
d_rightDivides_3064 ::
  T_IsQuasigroup_3038 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_3064 v0
  = case coe v0 of
      C_constructor_3112 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasigroup._.isEquivalence
d_isEquivalence_3068 ::
  T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3068 v0
  = coe d_isEquivalence_186 (coe d_isMagma_3056 (coe v0))
-- Algebra.Structures.IsQuasigroup._.isPartialEquivalence
d_isPartialEquivalence_3070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3070 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_3070 v7
du_isPartialEquivalence_3070 ::
  T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3070 v0
  = let v1 = d_isMagma_3056 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_186 (coe v1)))
-- Algebra.Structures.IsQuasigroup._.refl
d_refl_3072 :: T_IsQuasigroup_3038 -> AgdaAny -> AgdaAny
d_refl_3072 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_186 (coe d_isMagma_3056 (coe v0)))
-- Algebra.Structures.IsQuasigroup._.reflexive
d_reflexive_3074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3074 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_3074 v7
du_reflexive_3074 ::
  T_IsQuasigroup_3038 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3074 v0
  = let v1 = d_isMagma_3056 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_186 (coe v1)) v2)
-- Algebra.Structures.IsQuasigroup._.setoid
d_setoid_3076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3076 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_3076 v7
du_setoid_3076 ::
  T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3076 v0 = coe du_setoid_202 (coe d_isMagma_3056 (coe v0))
-- Algebra.Structures.IsQuasigroup._.sym
d_sym_3078 ::
  T_IsQuasigroup_3038 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3078 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_186 (coe d_isMagma_3056 (coe v0)))
-- Algebra.Structures.IsQuasigroup._.trans
d_trans_3080 ::
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3080 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_186 (coe d_isMagma_3056 (coe v0)))
-- Algebra.Structures.IsQuasigroup._.∙-cong
d_'8729''45'cong_3082 ::
  T_IsQuasigroup_3038 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3082 v0
  = coe d_'8729''45'cong_188 (coe d_isMagma_3056 (coe v0))
-- Algebra.Structures.IsQuasigroup._.∙-congʳ
d_'8729''45'cong'691'_3084 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3084 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_3084 v7
du_'8729''45'cong'691'_3084 ::
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3084 v0
  = let v1 = d_isMagma_3056 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsQuasigroup._.∙-congˡ
d_'8729''45'cong'737'_3086 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3086 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_3086 v7
du_'8729''45'cong'737'_3086 ::
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3086 v0
  = let v1 = d_isMagma_3056 (coe v0) in
    coe
      (let v2 = coe du_setoid_202 (coe v1) in
       coe
         (let v3 = d_'8729''45'cong_188 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
               (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v2))))))
-- Algebra.Structures.IsQuasigroup.\\-congˡ
d_'92''92''45'cong'737'_3088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_3088 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
                             v10 v11
  = du_'92''92''45'cong'737'_3088 v7 v8 v9 v10 v11
du_'92''92''45'cong'737'_3088 ::
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_3088 v0 v1 v2 v3 v4
  = coe
      d_'92''92''45'cong_3058 v0 v1 v1 v2 v3
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (d_isEquivalence_186 (coe d_isMagma_3056 (coe v0))) v1)
      v4
-- Algebra.Structures.IsQuasigroup.\\-congʳ
d_'92''92''45'cong'691'_3092 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_3092 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
                             v10 v11
  = du_'92''92''45'cong'691'_3092 v7 v8 v9 v10 v11
du_'92''92''45'cong'691'_3092 ::
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_3092 v0 v1 v2 v3 v4
  = coe
      d_'92''92''45'cong_3058 v0 v2 v3 v1 v1 v4
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (d_isEquivalence_186 (coe d_isMagma_3056 (coe v0))) v1)
-- Algebra.Structures.IsQuasigroup.//-congˡ
d_'47''47''45'cong'737'_3096 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3096 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
                             v10 v11
  = du_'47''47''45'cong'737'_3096 v7 v8 v9 v10 v11
du_'47''47''45'cong'737'_3096 ::
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3096 v0 v1 v2 v3 v4
  = coe
      d_'47''47''45'cong_3060 v0 v1 v1 v2 v3
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (d_isEquivalence_186 (coe d_isMagma_3056 (coe v0))) v1)
      v4
-- Algebra.Structures.IsQuasigroup.//-congʳ
d_'47''47''45'cong'691'_3100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
                             v10 v11
  = du_'47''47''45'cong'691'_3100 v7 v8 v9 v10 v11
du_'47''47''45'cong'691'_3100 ::
  T_IsQuasigroup_3038 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3100 v0 v1 v2 v3 v4
  = coe
      d_'47''47''45'cong_3060 v0 v2 v3 v1 v1 v4
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (d_isEquivalence_186 (coe d_isMagma_3056 (coe v0))) v1)
-- Algebra.Structures.IsQuasigroup.leftDividesˡ
d_leftDivides'737'_3104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_leftDivides'737'_3104 v7
du_leftDivides'737'_3104 ::
  T_IsQuasigroup_3038 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3104 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_leftDivides_3062 (coe v0))
-- Algebra.Structures.IsQuasigroup.leftDividesʳ
d_leftDivides'691'_3106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_leftDivides'691'_3106 v7
du_leftDivides'691'_3106 ::
  T_IsQuasigroup_3038 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3106 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_leftDivides_3062 (coe v0))
-- Algebra.Structures.IsQuasigroup.rightDividesˡ
d_rightDivides'737'_3108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_rightDivides'737'_3108 v7
du_rightDivides'737'_3108 ::
  T_IsQuasigroup_3038 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3108 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_rightDivides_3064 (coe v0))
-- Algebra.Structures.IsQuasigroup.rightDividesʳ
d_rightDivides'691'_3110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_3038 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3110 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_rightDivides'691'_3110 v7
du_rightDivides'691'_3110 ::
  T_IsQuasigroup_3038 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3110 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_rightDivides_3064 (coe v0))
-- Algebra.Structures.IsLoop
d_IsLoop_3122 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsLoop_3122
  = C_constructor_3192 T_IsQuasigroup_3038
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsLoop.isQuasigroup
d_isQuasigroup_3136 :: T_IsLoop_3122 -> T_IsQuasigroup_3038
d_isQuasigroup_3136 v0
  = case coe v0 of
      C_constructor_3192 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsLoop.identity
d_identity_3138 ::
  T_IsLoop_3122 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3138 v0
  = case coe v0 of
      C_constructor_3192 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsLoop._.//-cong
d_'47''47''45'cong_3142 ::
  T_IsLoop_3122 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_3142 v0
  = coe d_'47''47''45'cong_3060 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.//-congʳ
d_'47''47''45'cong'691'_3144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'691'_3144 v8
du_'47''47''45'cong'691'_3144 ::
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3144 v0
  = coe
      du_'47''47''45'cong'691'_3100 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.//-congˡ
d_'47''47''45'cong'737'_3146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'737'_3146 v8
du_'47''47''45'cong'737'_3146 ::
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3146 v0
  = coe
      du_'47''47''45'cong'737'_3096 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.\\-cong
d_'92''92''45'cong_3148 ::
  T_IsLoop_3122 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_3148 v0
  = coe d_'92''92''45'cong_3058 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.\\-congʳ
d_'92''92''45'cong'691'_3150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_3150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'691'_3150 v8
du_'92''92''45'cong'691'_3150 ::
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_3150 v0
  = coe
      du_'92''92''45'cong'691'_3092 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.\\-congˡ
d_'92''92''45'cong'737'_3152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_3152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'737'_3152 v8
du_'92''92''45'cong'737'_3152 ::
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_3152 v0
  = coe
      du_'92''92''45'cong'737'_3088 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.isEquivalence
d_isEquivalence_3154 ::
  T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3154 v0
  = coe
      d_isEquivalence_186
      (coe d_isMagma_3056 (coe d_isQuasigroup_3136 (coe v0)))
-- Algebra.Structures.IsLoop._.isMagma
d_isMagma_3156 :: T_IsLoop_3122 -> T_IsMagma_178
d_isMagma_3156 v0
  = coe d_isMagma_3056 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.isPartialEquivalence
d_isPartialEquivalence_3158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_3158 v8
du_isPartialEquivalence_3158 ::
  T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3158 v0
  = let v1 = d_isQuasigroup_3136 (coe v0) in
    coe
      (let v2 = d_isMagma_3056 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe d_isEquivalence_186 (coe v2))))
-- Algebra.Structures.IsLoop._.leftDivides
d_leftDivides_3160 ::
  T_IsLoop_3122 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_3160 v0
  = coe d_leftDivides_3062 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.leftDividesʳ
d_leftDivides'691'_3162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3122 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'691'_3162 v8
du_leftDivides'691'_3162 ::
  T_IsLoop_3122 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3162 v0
  = coe du_leftDivides'691'_3106 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.leftDividesˡ
d_leftDivides'737'_3164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3122 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'737'_3164 v8
du_leftDivides'737'_3164 ::
  T_IsLoop_3122 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3164 v0
  = coe du_leftDivides'737'_3104 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.refl
d_refl_3166 :: T_IsLoop_3122 -> AgdaAny -> AgdaAny
d_refl_3166 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe d_isMagma_3056 (coe d_isQuasigroup_3136 (coe v0))))
-- Algebra.Structures.IsLoop._.reflexive
d_reflexive_3168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3122 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_3168 v8
du_reflexive_3168 ::
  T_IsLoop_3122 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3168 v0
  = let v1 = d_isQuasigroup_3136 (coe v0) in
    coe
      (let v2 = d_isMagma_3056 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe d_isEquivalence_186 (coe v2)) v3))
-- Algebra.Structures.IsLoop._.rightDivides
d_rightDivides_3170 ::
  T_IsLoop_3122 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_3170 v0
  = coe d_rightDivides_3064 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.rightDividesʳ
d_rightDivides'691'_3172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3122 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'691'_3172 v8
du_rightDivides'691'_3172 ::
  T_IsLoop_3122 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3172 v0
  = coe du_rightDivides'691'_3110 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.rightDividesˡ
d_rightDivides'737'_3174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3122 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3174 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'737'_3174 v8
du_rightDivides'737'_3174 ::
  T_IsLoop_3122 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3174 v0
  = coe du_rightDivides'737'_3108 (coe d_isQuasigroup_3136 (coe v0))
-- Algebra.Structures.IsLoop._.setoid
d_setoid_3176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3122 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_3176 v8
du_setoid_3176 ::
  T_IsLoop_3122 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3176 v0
  = let v1 = d_isQuasigroup_3136 (coe v0) in
    coe (coe du_setoid_202 (coe d_isMagma_3056 (coe v1)))
-- Algebra.Structures.IsLoop._.sym
d_sym_3178 ::
  T_IsLoop_3122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3178 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe d_isMagma_3056 (coe d_isQuasigroup_3136 (coe v0))))
-- Algebra.Structures.IsLoop._.trans
d_trans_3180 ::
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3180 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe d_isMagma_3056 (coe d_isQuasigroup_3136 (coe v0))))
-- Algebra.Structures.IsLoop._.∙-cong
d_'8729''45'cong_3182 ::
  T_IsLoop_3122 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3182 v0
  = coe
      d_'8729''45'cong_188
      (coe d_isMagma_3056 (coe d_isQuasigroup_3136 (coe v0)))
-- Algebra.Structures.IsLoop._.∙-congʳ
d_'8729''45'cong'691'_3184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3184 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_3184 v8
du_'8729''45'cong'691'_3184 ::
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3184 v0
  = let v1 = d_isQuasigroup_3136 (coe v0) in
    coe
      (let v2 = d_isMagma_3056 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsLoop._.∙-congˡ
d_'8729''45'cong'737'_3186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3186 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_3186 v8
du_'8729''45'cong'737'_3186 ::
  T_IsLoop_3122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3186 v0
  = let v1 = d_isQuasigroup_3136 (coe v0) in
    coe
      (let v2 = d_isMagma_3056 (coe v1) in
       coe
         (let v3 = coe du_setoid_202 (coe v2) in
          coe
            (let v4 = d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.IsLoop.identityˡ
d_identity'737'_3188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3122 -> AgdaAny -> AgdaAny
d_identity'737'_3188 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_3188 v8
du_identity'737'_3188 :: T_IsLoop_3122 -> AgdaAny -> AgdaAny
du_identity'737'_3188 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_identity_3138 (coe v0))
-- Algebra.Structures.IsLoop.identityʳ
d_identity'691'_3190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3122 -> AgdaAny -> AgdaAny
d_identity'691'_3190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_3190 v8
du_identity'691'_3190 :: T_IsLoop_3122 -> AgdaAny -> AgdaAny
du_identity'691'_3190 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_identity_3138 (coe v0))
-- Algebra.Structures.IsLeftBolLoop
d_IsLeftBolLoop_3202 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsLeftBolLoop_3202
  = C_constructor_3276 T_IsLoop_3122
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsLeftBolLoop.isLoop
d_isLoop_3216 :: T_IsLeftBolLoop_3202 -> T_IsLoop_3122
d_isLoop_3216 v0
  = case coe v0 of
      C_constructor_3276 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsLeftBolLoop.leftBol
d_leftBol_3218 ::
  T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_leftBol_3218 v0
  = case coe v0 of
      C_constructor_3276 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsLeftBolLoop._.//-cong
d_'47''47''45'cong_3222 ::
  T_IsLeftBolLoop_3202 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_3222 v0
  = coe
      d_'47''47''45'cong_3060
      (coe d_isQuasigroup_3136 (coe d_isLoop_3216 (coe v0)))
-- Algebra.Structures.IsLeftBolLoop._.//-congʳ
d_'47''47''45'cong'691'_3224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'691'_3224 v8
du_'47''47''45'cong'691'_3224 ::
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3224 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'691'_3100 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.//-congˡ
d_'47''47''45'cong'737'_3226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'737'_3226 v8
du_'47''47''45'cong'737'_3226 ::
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3226 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'737'_3096 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.\\-cong
d_'92''92''45'cong_3228 ::
  T_IsLeftBolLoop_3202 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_3228 v0
  = coe
      d_'92''92''45'cong_3058
      (coe d_isQuasigroup_3136 (coe d_isLoop_3216 (coe v0)))
-- Algebra.Structures.IsLeftBolLoop._.\\-congʳ
d_'92''92''45'cong'691'_3230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_3230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'691'_3230 v8
du_'92''92''45'cong'691'_3230 ::
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_3230 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'691'_3092 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.\\-congˡ
d_'92''92''45'cong'737'_3232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_3232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'737'_3232 v8
du_'92''92''45'cong'737'_3232 ::
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_3232 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'737'_3088 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.identity
d_identity_3234 ::
  T_IsLeftBolLoop_3202 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3234 v0
  = coe d_identity_3138 (coe d_isLoop_3216 (coe v0))
-- Algebra.Structures.IsLeftBolLoop._.identityʳ
d_identity'691'_3236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny
d_identity'691'_3236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_3236 v8
du_identity'691'_3236 :: T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny
du_identity'691'_3236 v0
  = coe du_identity'691'_3190 (coe d_isLoop_3216 (coe v0))
-- Algebra.Structures.IsLeftBolLoop._.identityˡ
d_identity'737'_3238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny
d_identity'737'_3238 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_3238 v8
du_identity'737'_3238 :: T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny
du_identity'737'_3238 v0
  = coe du_identity'737'_3188 (coe d_isLoop_3216 (coe v0))
-- Algebra.Structures.IsLeftBolLoop._.isEquivalence
d_isEquivalence_3240 ::
  T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3240 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_3056
         (coe d_isQuasigroup_3136 (coe d_isLoop_3216 (coe v0))))
-- Algebra.Structures.IsLeftBolLoop._.isMagma
d_isMagma_3242 :: T_IsLeftBolLoop_3202 -> T_IsMagma_178
d_isMagma_3242 v0
  = coe
      d_isMagma_3056
      (coe d_isQuasigroup_3136 (coe d_isLoop_3216 (coe v0)))
-- Algebra.Structures.IsLeftBolLoop._.isPartialEquivalence
d_isPartialEquivalence_3244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_3244 v8
du_isPartialEquivalence_3244 ::
  T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3244 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.IsLeftBolLoop._.isQuasigroup
d_isQuasigroup_3246 :: T_IsLeftBolLoop_3202 -> T_IsQuasigroup_3038
d_isQuasigroup_3246 v0
  = coe d_isQuasigroup_3136 (coe d_isLoop_3216 (coe v0))
-- Algebra.Structures.IsLeftBolLoop._.leftDivides
d_leftDivides_3248 ::
  T_IsLeftBolLoop_3202 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_3248 v0
  = coe
      d_leftDivides_3062
      (coe d_isQuasigroup_3136 (coe d_isLoop_3216 (coe v0)))
-- Algebra.Structures.IsLeftBolLoop._.leftDividesʳ
d_leftDivides'691'_3250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'691'_3250 v8
du_leftDivides'691'_3250 ::
  T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3250 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (coe du_leftDivides'691'_3106 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.leftDividesˡ
d_leftDivides'737'_3252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'737'_3252 v8
du_leftDivides'737'_3252 ::
  T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3252 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (coe du_leftDivides'737'_3104 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.refl
d_refl_3254 :: T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny
d_refl_3254 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe d_isQuasigroup_3136 (coe d_isLoop_3216 (coe v0)))))
-- Algebra.Structures.IsLeftBolLoop._.reflexive
d_reflexive_3256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3202 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_3256 v8
du_reflexive_3256 ::
  T_IsLeftBolLoop_3202 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3256 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_186 (coe v3)) v4)))
-- Algebra.Structures.IsLeftBolLoop._.rightDivides
d_rightDivides_3258 ::
  T_IsLeftBolLoop_3202 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_3258 v0
  = coe
      d_rightDivides_3064
      (coe d_isQuasigroup_3136 (coe d_isLoop_3216 (coe v0)))
-- Algebra.Structures.IsLeftBolLoop._.rightDividesʳ
d_rightDivides'691'_3260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'691'_3260 v8
du_rightDivides'691'_3260 ::
  T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3260 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (coe du_rightDivides'691'_3110 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.rightDividesˡ
d_rightDivides'737'_3262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'737'_3262 v8
du_rightDivides'737'_3262 ::
  T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3262 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (coe du_rightDivides'737'_3108 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.setoid
d_setoid_3264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_3264 v8
du_setoid_3264 ::
  T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3264 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe (coe du_setoid_202 (coe d_isMagma_3056 (coe v2))))
-- Algebra.Structures.IsLeftBolLoop._.sym
d_sym_3266 ::
  T_IsLeftBolLoop_3202 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3266 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe d_isQuasigroup_3136 (coe d_isLoop_3216 (coe v0)))))
-- Algebra.Structures.IsLeftBolLoop._.trans
d_trans_3268 ::
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3268 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe d_isQuasigroup_3136 (coe d_isLoop_3216 (coe v0)))))
-- Algebra.Structures.IsLeftBolLoop._.∙-cong
d_'8729''45'cong_3270 ::
  T_IsLeftBolLoop_3202 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3270 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_3056
         (coe d_isQuasigroup_3136 (coe d_isLoop_3216 (coe v0))))
-- Algebra.Structures.IsLeftBolLoop._.∙-congʳ
d_'8729''45'cong'691'_3272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_3272 v8
du_'8729''45'cong'691'_3272 ::
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3272 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsLeftBolLoop._.∙-congˡ
d_'8729''45'cong'737'_3274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_3274 v8
du_'8729''45'cong'737'_3274 ::
  T_IsLeftBolLoop_3202 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3274 v0
  = let v1 = d_isLoop_3216 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsRightBolLoop
d_IsRightBolLoop_3286 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsRightBolLoop_3286
  = C_constructor_3360 T_IsLoop_3122
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsRightBolLoop.isLoop
d_isLoop_3300 :: T_IsRightBolLoop_3286 -> T_IsLoop_3122
d_isLoop_3300 v0
  = case coe v0 of
      C_constructor_3360 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRightBolLoop.rightBol
d_rightBol_3302 ::
  T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_rightBol_3302 v0
  = case coe v0 of
      C_constructor_3360 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRightBolLoop._.//-cong
d_'47''47''45'cong_3306 ::
  T_IsRightBolLoop_3286 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_3306 v0
  = coe
      d_'47''47''45'cong_3060
      (coe d_isQuasigroup_3136 (coe d_isLoop_3300 (coe v0)))
-- Algebra.Structures.IsRightBolLoop._.//-congʳ
d_'47''47''45'cong'691'_3308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'691'_3308 v8
du_'47''47''45'cong'691'_3308 ::
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3308 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'691'_3100 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.//-congˡ
d_'47''47''45'cong'737'_3310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'737'_3310 v8
du_'47''47''45'cong'737'_3310 ::
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3310 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'737'_3096 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.\\-cong
d_'92''92''45'cong_3312 ::
  T_IsRightBolLoop_3286 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_3312 v0
  = coe
      d_'92''92''45'cong_3058
      (coe d_isQuasigroup_3136 (coe d_isLoop_3300 (coe v0)))
-- Algebra.Structures.IsRightBolLoop._.\\-congʳ
d_'92''92''45'cong'691'_3314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_3314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'691'_3314 v8
du_'92''92''45'cong'691'_3314 ::
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_3314 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'691'_3092 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.\\-congˡ
d_'92''92''45'cong'737'_3316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_3316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'737'_3316 v8
du_'92''92''45'cong'737'_3316 ::
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_3316 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'737'_3088 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.identity
d_identity_3318 ::
  T_IsRightBolLoop_3286 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3318 v0
  = coe d_identity_3138 (coe d_isLoop_3300 (coe v0))
-- Algebra.Structures.IsRightBolLoop._.identityʳ
d_identity'691'_3320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny
d_identity'691'_3320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_3320 v8
du_identity'691'_3320 ::
  T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny
du_identity'691'_3320 v0
  = coe du_identity'691'_3190 (coe d_isLoop_3300 (coe v0))
-- Algebra.Structures.IsRightBolLoop._.identityˡ
d_identity'737'_3322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny
d_identity'737'_3322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_3322 v8
du_identity'737'_3322 ::
  T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny
du_identity'737'_3322 v0
  = coe du_identity'737'_3188 (coe d_isLoop_3300 (coe v0))
-- Algebra.Structures.IsRightBolLoop._.isEquivalence
d_isEquivalence_3324 ::
  T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3324 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_3056
         (coe d_isQuasigroup_3136 (coe d_isLoop_3300 (coe v0))))
-- Algebra.Structures.IsRightBolLoop._.isMagma
d_isMagma_3326 :: T_IsRightBolLoop_3286 -> T_IsMagma_178
d_isMagma_3326 v0
  = coe
      d_isMagma_3056
      (coe d_isQuasigroup_3136 (coe d_isLoop_3300 (coe v0)))
-- Algebra.Structures.IsRightBolLoop._.isPartialEquivalence
d_isPartialEquivalence_3328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_3328 v8
du_isPartialEquivalence_3328 ::
  T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3328 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.IsRightBolLoop._.isQuasigroup
d_isQuasigroup_3330 :: T_IsRightBolLoop_3286 -> T_IsQuasigroup_3038
d_isQuasigroup_3330 v0
  = coe d_isQuasigroup_3136 (coe d_isLoop_3300 (coe v0))
-- Algebra.Structures.IsRightBolLoop._.leftDivides
d_leftDivides_3332 ::
  T_IsRightBolLoop_3286 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_3332 v0
  = coe
      d_leftDivides_3062
      (coe d_isQuasigroup_3136 (coe d_isLoop_3300 (coe v0)))
-- Algebra.Structures.IsRightBolLoop._.leftDividesʳ
d_leftDivides'691'_3334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'691'_3334 v8
du_leftDivides'691'_3334 ::
  T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3334 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (coe du_leftDivides'691'_3106 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.leftDividesˡ
d_leftDivides'737'_3336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'737'_3336 v8
du_leftDivides'737'_3336 ::
  T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3336 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (coe du_leftDivides'737'_3104 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.refl
d_refl_3338 :: T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny
d_refl_3338 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe d_isQuasigroup_3136 (coe d_isLoop_3300 (coe v0)))))
-- Algebra.Structures.IsRightBolLoop._.reflexive
d_reflexive_3340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3286 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_3340 v8
du_reflexive_3340 ::
  T_IsRightBolLoop_3286 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3340 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_186 (coe v3)) v4)))
-- Algebra.Structures.IsRightBolLoop._.rightDivides
d_rightDivides_3342 ::
  T_IsRightBolLoop_3286 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_3342 v0
  = coe
      d_rightDivides_3064
      (coe d_isQuasigroup_3136 (coe d_isLoop_3300 (coe v0)))
-- Algebra.Structures.IsRightBolLoop._.rightDividesʳ
d_rightDivides'691'_3344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'691'_3344 v8
du_rightDivides'691'_3344 ::
  T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3344 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (coe du_rightDivides'691'_3110 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.rightDividesˡ
d_rightDivides'737'_3346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'737'_3346 v8
du_rightDivides'737'_3346 ::
  T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3346 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (coe du_rightDivides'737'_3108 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.setoid
d_setoid_3348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_3348 v8
du_setoid_3348 ::
  T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3348 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe (coe du_setoid_202 (coe d_isMagma_3056 (coe v2))))
-- Algebra.Structures.IsRightBolLoop._.sym
d_sym_3350 ::
  T_IsRightBolLoop_3286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3350 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe d_isQuasigroup_3136 (coe d_isLoop_3300 (coe v0)))))
-- Algebra.Structures.IsRightBolLoop._.trans
d_trans_3352 ::
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3352 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe d_isQuasigroup_3136 (coe d_isLoop_3300 (coe v0)))))
-- Algebra.Structures.IsRightBolLoop._.∙-cong
d_'8729''45'cong_3354 ::
  T_IsRightBolLoop_3286 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3354 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_3056
         (coe d_isQuasigroup_3136 (coe d_isLoop_3300 (coe v0))))
-- Algebra.Structures.IsRightBolLoop._.∙-congʳ
d_'8729''45'cong'691'_3356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_3356 v8
du_'8729''45'cong'691'_3356 ::
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3356 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsRightBolLoop._.∙-congˡ
d_'8729''45'cong'737'_3358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_3358 v8
du_'8729''45'cong'737'_3358 ::
  T_IsRightBolLoop_3286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3358 v0
  = let v1 = d_isLoop_3300 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsMoufangLoop
d_IsMoufangLoop_3370 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsMoufangLoop_3370
  = C_constructor_3452 T_IsLeftBolLoop_3202
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsMoufangLoop.isLeftBolLoop
d_isLeftBolLoop_3386 ::
  T_IsMoufangLoop_3370 -> T_IsLeftBolLoop_3202
d_isLeftBolLoop_3386 v0
  = case coe v0 of
      C_constructor_3452 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMoufangLoop.rightBol
d_rightBol_3388 ::
  T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_rightBol_3388 v0
  = case coe v0 of
      C_constructor_3452 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMoufangLoop.identical
d_identical_3390 ::
  T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identical_3390 v0
  = case coe v0 of
      C_constructor_3452 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMoufangLoop._.//-cong
d_'47''47''45'cong_3394 ::
  T_IsMoufangLoop_3370 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_3394 v0
  = coe
      d_'47''47''45'cong_3060
      (coe
         d_isQuasigroup_3136
         (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0))))
-- Algebra.Structures.IsMoufangLoop._.//-congʳ
d_'47''47''45'cong'691'_3396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'691'_3396 v8
du_'47''47''45'cong'691'_3396 ::
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3396 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (coe
            du_'47''47''45'cong'691'_3100 (coe d_isQuasigroup_3136 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.//-congˡ
d_'47''47''45'cong'737'_3398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'737'_3398 v8
du_'47''47''45'cong'737'_3398 ::
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3398 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (coe
            du_'47''47''45'cong'737'_3096 (coe d_isQuasigroup_3136 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.\\-cong
d_'92''92''45'cong_3400 ::
  T_IsMoufangLoop_3370 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_3400 v0
  = coe
      d_'92''92''45'cong_3058
      (coe
         d_isQuasigroup_3136
         (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0))))
-- Algebra.Structures.IsMoufangLoop._.\\-congʳ
d_'92''92''45'cong'691'_3402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_3402 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'691'_3402 v8
du_'92''92''45'cong'691'_3402 ::
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_3402 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (coe
            du_'92''92''45'cong'691'_3092 (coe d_isQuasigroup_3136 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.\\-congˡ
d_'92''92''45'cong'737'_3404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_3404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'737'_3404 v8
du_'92''92''45'cong'737'_3404 ::
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_3404 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (coe
            du_'92''92''45'cong'737'_3088 (coe d_isQuasigroup_3136 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.identity
d_identity_3406 ::
  T_IsMoufangLoop_3370 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3406 v0
  = coe
      d_identity_3138
      (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0)))
-- Algebra.Structures.IsMoufangLoop._.identityʳ
d_identity'691'_3408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny
d_identity'691'_3408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_3408 v8
du_identity'691'_3408 :: T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny
du_identity'691'_3408 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe (coe du_identity'691'_3190 (coe d_isLoop_3216 (coe v1)))
-- Algebra.Structures.IsMoufangLoop._.identityˡ
d_identity'737'_3410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny
d_identity'737'_3410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_3410 v8
du_identity'737'_3410 :: T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny
du_identity'737'_3410 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe (coe du_identity'737'_3188 (coe d_isLoop_3216 (coe v1)))
-- Algebra.Structures.IsMoufangLoop._.isEquivalence
d_isEquivalence_3412 ::
  T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3412 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_3056
         (coe
            d_isQuasigroup_3136
            (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0)))))
-- Algebra.Structures.IsMoufangLoop._.isLoop
d_isLoop_3414 :: T_IsMoufangLoop_3370 -> T_IsLoop_3122
d_isLoop_3414 v0
  = coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0))
-- Algebra.Structures.IsMoufangLoop._.isMagma
d_isMagma_3416 :: T_IsMoufangLoop_3370 -> T_IsMagma_178
d_isMagma_3416 v0
  = coe
      d_isMagma_3056
      (coe
         d_isQuasigroup_3136
         (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0))))
-- Algebra.Structures.IsMoufangLoop._.isPartialEquivalence
d_isPartialEquivalence_3418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_3418 v8
du_isPartialEquivalence_3418 ::
  T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3418 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (let v3 = d_isQuasigroup_3136 (coe v2) in
          coe
            (let v4 = d_isMagma_3056 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe d_isEquivalence_186 (coe v4))))))
-- Algebra.Structures.IsMoufangLoop._.isQuasigroup
d_isQuasigroup_3420 :: T_IsMoufangLoop_3370 -> T_IsQuasigroup_3038
d_isQuasigroup_3420 v0
  = coe
      d_isQuasigroup_3136
      (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0)))
-- Algebra.Structures.IsMoufangLoop._.leftBol
d_leftBol_3422 ::
  T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_leftBol_3422 v0
  = coe d_leftBol_3218 (coe d_isLeftBolLoop_3386 (coe v0))
-- Algebra.Structures.IsMoufangLoop._.leftDivides
d_leftDivides_3424 ::
  T_IsMoufangLoop_3370 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_3424 v0
  = coe
      d_leftDivides_3062
      (coe
         d_isQuasigroup_3136
         (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0))))
-- Algebra.Structures.IsMoufangLoop._.leftDividesʳ
d_leftDivides'691'_3426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3426 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'691'_3426 v8
du_leftDivides'691'_3426 ::
  T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3426 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (coe du_leftDivides'691'_3106 (coe d_isQuasigroup_3136 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.leftDividesˡ
d_leftDivides'737'_3428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'737'_3428 v8
du_leftDivides'737'_3428 ::
  T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3428 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (coe du_leftDivides'737'_3104 (coe d_isQuasigroup_3136 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.refl
d_refl_3430 :: T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny
d_refl_3430 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe
               d_isQuasigroup_3136
               (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0))))))
-- Algebra.Structures.IsMoufangLoop._.reflexive
d_reflexive_3432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3370 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3432 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_3432 v8
du_reflexive_3432 ::
  T_IsMoufangLoop_3370 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3432 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (let v3 = d_isQuasigroup_3136 (coe v2) in
          coe
            (let v4 = d_isMagma_3056 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe d_isEquivalence_186 (coe v4)) v5))))
-- Algebra.Structures.IsMoufangLoop._.rightDivides
d_rightDivides_3434 ::
  T_IsMoufangLoop_3370 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_3434 v0
  = coe
      d_rightDivides_3064
      (coe
         d_isQuasigroup_3136
         (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0))))
-- Algebra.Structures.IsMoufangLoop._.rightDividesʳ
d_rightDivides'691'_3436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'691'_3436 v8
du_rightDivides'691'_3436 ::
  T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3436 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (coe du_rightDivides'691'_3110 (coe d_isQuasigroup_3136 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.rightDividesˡ
d_rightDivides'737'_3438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'737'_3438 v8
du_rightDivides'737'_3438 ::
  T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3438 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (coe du_rightDivides'737'_3108 (coe d_isQuasigroup_3136 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.setoid
d_setoid_3440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_3440 v8
du_setoid_3440 ::
  T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3440 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (let v3 = d_isQuasigroup_3136 (coe v2) in
          coe (coe du_setoid_202 (coe d_isMagma_3056 (coe v3)))))
-- Algebra.Structures.IsMoufangLoop._.sym
d_sym_3442 ::
  T_IsMoufangLoop_3370 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3442 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe
               d_isQuasigroup_3136
               (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0))))))
-- Algebra.Structures.IsMoufangLoop._.trans
d_trans_3444 ::
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3444 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe
               d_isQuasigroup_3136
               (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0))))))
-- Algebra.Structures.IsMoufangLoop._.∙-cong
d_'8729''45'cong_3446 ::
  T_IsMoufangLoop_3370 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3446 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_3056
         (coe
            d_isQuasigroup_3136
            (coe d_isLoop_3216 (coe d_isLeftBolLoop_3386 (coe v0)))))
-- Algebra.Structures.IsMoufangLoop._.∙-congʳ
d_'8729''45'cong'691'_3448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3448 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_3448 v8
du_'8729''45'cong'691'_3448 ::
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3448 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (let v3 = d_isQuasigroup_3136 (coe v2) in
          coe
            (let v4 = d_isMagma_3056 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsMoufangLoop._.∙-congˡ
d_'8729''45'cong'737'_3450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_3450 v8
du_'8729''45'cong'737'_3450 ::
  T_IsMoufangLoop_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3450 v0
  = let v1 = d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = d_isLoop_3216 (coe v1) in
       coe
         (let v3 = d_isQuasigroup_3136 (coe v2) in
          coe
            (let v4 = d_isMagma_3056 (coe v3) in
             coe
               (let v5 = coe du_setoid_202 (coe v4) in
                coe
                  (let v6 = d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.IsMiddleBolLoop
d_IsMiddleBolLoop_3462 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsMiddleBolLoop_3462
  = C_constructor_3536 T_IsLoop_3122
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsMiddleBolLoop.isLoop
d_isLoop_3476 :: T_IsMiddleBolLoop_3462 -> T_IsLoop_3122
d_isLoop_3476 v0
  = case coe v0 of
      C_constructor_3536 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMiddleBolLoop.middleBol
d_middleBol_3478 ::
  T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_middleBol_3478 v0
  = case coe v0 of
      C_constructor_3536 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMiddleBolLoop._.//-cong
d_'47''47''45'cong_3482 ::
  T_IsMiddleBolLoop_3462 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_3482 v0
  = coe
      d_'47''47''45'cong_3060
      (coe d_isQuasigroup_3136 (coe d_isLoop_3476 (coe v0)))
-- Algebra.Structures.IsMiddleBolLoop._.//-congʳ
d_'47''47''45'cong'691'_3484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'691'_3484 v8
du_'47''47''45'cong'691'_3484 ::
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3484 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'691'_3100 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.//-congˡ
d_'47''47''45'cong'737'_3486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3486 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'737'_3486 v8
du_'47''47''45'cong'737'_3486 ::
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3486 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'737'_3096 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.\\-cong
d_'92''92''45'cong_3488 ::
  T_IsMiddleBolLoop_3462 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_3488 v0
  = coe
      d_'92''92''45'cong_3058
      (coe d_isQuasigroup_3136 (coe d_isLoop_3476 (coe v0)))
-- Algebra.Structures.IsMiddleBolLoop._.\\-congʳ
d_'92''92''45'cong'691'_3490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_3490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'691'_3490 v8
du_'92''92''45'cong'691'_3490 ::
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_3490 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'691'_3092 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.\\-congˡ
d_'92''92''45'cong'737'_3492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_3492 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'737'_3492 v8
du_'92''92''45'cong'737'_3492 ::
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_3492 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'737'_3088 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.identity
d_identity_3494 ::
  T_IsMiddleBolLoop_3462 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3494 v0
  = coe d_identity_3138 (coe d_isLoop_3476 (coe v0))
-- Algebra.Structures.IsMiddleBolLoop._.identityʳ
d_identity'691'_3496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny
d_identity'691'_3496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_3496 v8
du_identity'691'_3496 ::
  T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny
du_identity'691'_3496 v0
  = coe du_identity'691'_3190 (coe d_isLoop_3476 (coe v0))
-- Algebra.Structures.IsMiddleBolLoop._.identityˡ
d_identity'737'_3498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny
d_identity'737'_3498 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_3498 v8
du_identity'737'_3498 ::
  T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny
du_identity'737'_3498 v0
  = coe du_identity'737'_3188 (coe d_isLoop_3476 (coe v0))
-- Algebra.Structures.IsMiddleBolLoop._.isEquivalence
d_isEquivalence_3500 ::
  T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3500 v0
  = coe
      d_isEquivalence_186
      (coe
         d_isMagma_3056
         (coe d_isQuasigroup_3136 (coe d_isLoop_3476 (coe v0))))
-- Algebra.Structures.IsMiddleBolLoop._.isMagma
d_isMagma_3502 :: T_IsMiddleBolLoop_3462 -> T_IsMagma_178
d_isMagma_3502 v0
  = coe
      d_isMagma_3056
      (coe d_isQuasigroup_3136 (coe d_isLoop_3476 (coe v0)))
-- Algebra.Structures.IsMiddleBolLoop._.isPartialEquivalence
d_isPartialEquivalence_3504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3504 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_3504 v8
du_isPartialEquivalence_3504 ::
  T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3504 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.IsMiddleBolLoop._.isQuasigroup
d_isQuasigroup_3506 ::
  T_IsMiddleBolLoop_3462 -> T_IsQuasigroup_3038
d_isQuasigroup_3506 v0
  = coe d_isQuasigroup_3136 (coe d_isLoop_3476 (coe v0))
-- Algebra.Structures.IsMiddleBolLoop._.leftDivides
d_leftDivides_3508 ::
  T_IsMiddleBolLoop_3462 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_3508 v0
  = coe
      d_leftDivides_3062
      (coe d_isQuasigroup_3136 (coe d_isLoop_3476 (coe v0)))
-- Algebra.Structures.IsMiddleBolLoop._.leftDividesʳ
d_leftDivides'691'_3510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'691'_3510 v8
du_leftDivides'691'_3510 ::
  T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3510 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (coe du_leftDivides'691'_3106 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.leftDividesˡ
d_leftDivides'737'_3512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'737'_3512 v8
du_leftDivides'737'_3512 ::
  T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3512 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (coe du_leftDivides'737'_3104 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.refl
d_refl_3514 :: T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny
d_refl_3514 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe d_isQuasigroup_3136 (coe d_isLoop_3476 (coe v0)))))
-- Algebra.Structures.IsMiddleBolLoop._.reflexive
d_reflexive_3516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3462 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_3516 v8
du_reflexive_3516 ::
  T_IsMiddleBolLoop_3462 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3516 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_186 (coe v3)) v4)))
-- Algebra.Structures.IsMiddleBolLoop._.rightDivides
d_rightDivides_3518 ::
  T_IsMiddleBolLoop_3462 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_3518 v0
  = coe
      d_rightDivides_3064
      (coe d_isQuasigroup_3136 (coe d_isLoop_3476 (coe v0)))
-- Algebra.Structures.IsMiddleBolLoop._.rightDividesʳ
d_rightDivides'691'_3520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'691'_3520 v8
du_rightDivides'691'_3520 ::
  T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3520 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (coe du_rightDivides'691'_3110 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.rightDividesˡ
d_rightDivides'737'_3522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3522 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'737'_3522 v8
du_rightDivides'737'_3522 ::
  T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3522 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (coe du_rightDivides'737'_3108 (coe d_isQuasigroup_3136 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.setoid
d_setoid_3524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3524 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_3524 v8
du_setoid_3524 ::
  T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3524 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe (coe du_setoid_202 (coe d_isMagma_3056 (coe v2))))
-- Algebra.Structures.IsMiddleBolLoop._.sym
d_sym_3526 ::
  T_IsMiddleBolLoop_3462 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3526 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe d_isQuasigroup_3136 (coe d_isLoop_3476 (coe v0)))))
-- Algebra.Structures.IsMiddleBolLoop._.trans
d_trans_3528 ::
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3528 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_186
         (coe
            d_isMagma_3056
            (coe d_isQuasigroup_3136 (coe d_isLoop_3476 (coe v0)))))
-- Algebra.Structures.IsMiddleBolLoop._.∙-cong
d_'8729''45'cong_3530 ::
  T_IsMiddleBolLoop_3462 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3530 v0
  = coe
      d_'8729''45'cong_188
      (coe
         d_isMagma_3056
         (coe d_isQuasigroup_3136 (coe d_isLoop_3476 (coe v0))))
-- Algebra.Structures.IsMiddleBolLoop._.∙-congʳ
d_'8729''45'cong'691'_3532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_3532 v8
du_'8729''45'cong'691'_3532 ::
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3532 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.IsMiddleBolLoop._.∙-congˡ
d_'8729''45'cong'737'_3534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3534 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_3534 v8
du_'8729''45'cong'737'_3534 ::
  T_IsMiddleBolLoop_3462 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3534 v0
  = let v1 = d_isLoop_3476 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3 = d_isMagma_3056 (coe v2) in
          coe
            (let v4 = coe du_setoid_202 (coe v3) in
             coe
               (let v5 = d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
