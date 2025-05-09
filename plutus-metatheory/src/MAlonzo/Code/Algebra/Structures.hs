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

module MAlonzo.Code.Algebra.Structures where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Consequences.Setoid qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
  = C_IsSuccessorSet'46'constructor_817 MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
                                        (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsSuccessorSet.isEquivalence
d_isEquivalence_156 ::
  T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_156 v0
  = case coe v0 of
      C_IsSuccessorSet'46'constructor_817 v1 v2 -> coe v1
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSuccessorSet.suc#-cong
d_suc'35''45'cong_158 ::
  T_IsSuccessorSet_146 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_suc'35''45'cong_158 v0
  = case coe v0 of
      C_IsSuccessorSet'46'constructor_817 v1 v2 -> coe v2
      _                                         -> MAlonzo.RTE.mazUnreachableError
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
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
      (coe d_isEquivalence_156 (coe v0))
-- Algebra.Structures.IsSuccessorSet._.refl
d_refl_164 :: T_IsSuccessorSet_146 -> AgdaAny -> AgdaAny
d_refl_164 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
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
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
      (coe d_isEquivalence_156 (coe v0)) v1
-- Algebra.Structures.IsSuccessorSet._.sym
d_sym_168 ::
  T_IsSuccessorSet_146 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_168 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_156 (coe v0))
-- Algebra.Structures.IsSuccessorSet._.trans
d_trans_170 ::
  T_IsSuccessorSet_146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_170 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
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
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_172 v6
du_setoid_172 ::
  T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_172 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      (d_isEquivalence_156 (coe v0))
-- Algebra.Structures.IsMagma
d_IsMagma_176 a0 a1 a2 a3 a4 = ()
data T_IsMagma_176
  = C_IsMagma'46'constructor_1867 MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
                                  (AgdaAny ->
                                   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsMagma.isEquivalence
d_isEquivalence_184 ::
  T_IsMagma_176 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_184 v0
  = case coe v0 of
      C_IsMagma'46'constructor_1867 v1 v2 -> coe v1
      _                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMagma.∙-cong
d_'8729''45'cong_186 ::
  T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_186 v0
  = case coe v0 of
      C_IsMagma'46'constructor_1867 v1 v2 -> coe v2
      _                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMagma._.isPartialEquivalence
d_isPartialEquivalence_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMagma_176 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_190 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_190 v5
du_isPartialEquivalence_190 ::
  T_IsMagma_176 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_190 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
      (coe d_isEquivalence_184 (coe v0))
-- Algebra.Structures.IsMagma._.refl
d_refl_192 :: T_IsMagma_176 -> AgdaAny -> AgdaAny
d_refl_192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe v0))
-- Algebra.Structures.IsMagma._.reflexive
d_reflexive_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_194 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_194 v5
du_reflexive_194 ::
  T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_194 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
      (coe d_isEquivalence_184 (coe v0)) v1
-- Algebra.Structures.IsMagma._.sym
d_sym_196 ::
  T_IsMagma_176 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_196 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe v0))
-- Algebra.Structures.IsMagma._.trans
d_trans_198 ::
  T_IsMagma_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_198 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe v0))
-- Algebra.Structures.IsMagma.setoid
d_setoid_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMagma_176 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_200 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_200 v5
du_setoid_200 ::
  T_IsMagma_176 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_200 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      (d_isEquivalence_184 (coe v0))
-- Algebra.Structures.IsMagma.∙-congˡ
d_'8729''45'cong'737'_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMagma_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_202 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_'8729''45'cong'737'_202 v5 v6 v7 v8 v9
du_'8729''45'cong'737'_202 ::
  T_IsMagma_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_202 v0 v1 v2 v3 v4
  = coe
      d_'8729''45'cong_186 v0 v1 v1 v2 v3
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (d_isEquivalence_184 (coe v0)) v1)
      v4
-- Algebra.Structures.IsMagma.∙-congʳ
d_'8729''45'cong'691'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMagma_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_206 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_'8729''45'cong'691'_206 v5 v6 v7 v8 v9
du_'8729''45'cong'691'_206 ::
  T_IsMagma_176 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_206 v0 v1 v2 v3 v4
  = coe
      d_'8729''45'cong_186 v0 v2 v3 v1 v1 v4
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (d_isEquivalence_184 (coe v0)) v1)
-- Algebra.Structures.IsCommutativeMagma
d_IsCommutativeMagma_212 a0 a1 a2 a3 a4 = ()
data T_IsCommutativeMagma_212
  = C_IsCommutativeMagma'46'constructor_3749 T_IsMagma_176
                                             (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeMagma.isMagma
d_isMagma_220 :: T_IsCommutativeMagma_212 -> T_IsMagma_176
d_isMagma_220 v0
  = case coe v0 of
      C_IsCommutativeMagma'46'constructor_3749 v1 v2 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeMagma.comm
d_comm_222 ::
  T_IsCommutativeMagma_212 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_222 v0
  = case coe v0 of
      C_IsCommutativeMagma'46'constructor_3749 v1 v2 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeMagma._.isEquivalence
d_isEquivalence_226 ::
  T_IsCommutativeMagma_212 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_226 v0
  = coe d_isEquivalence_184 (coe d_isMagma_220 (coe v0))
-- Algebra.Structures.IsCommutativeMagma._.isPartialEquivalence
d_isPartialEquivalence_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeMagma_212 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_228 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_228 v5
du_isPartialEquivalence_228 ::
  T_IsCommutativeMagma_212 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_228 v0
  = let v1 = d_isMagma_220 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_184 (coe v1)))
-- Algebra.Structures.IsCommutativeMagma._.refl
d_refl_230 :: T_IsCommutativeMagma_212 -> AgdaAny -> AgdaAny
d_refl_230 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe d_isMagma_220 (coe v0)))
-- Algebra.Structures.IsCommutativeMagma._.reflexive
d_reflexive_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeMagma_212 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_232 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_232 v5
du_reflexive_232 ::
  T_IsCommutativeMagma_212 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_232 v0
  = let v1 = d_isMagma_220 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_184 (coe v1)) v2)
-- Algebra.Structures.IsCommutativeMagma._.setoid
d_setoid_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeMagma_212 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_234 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_234 v5
du_setoid_234 ::
  T_IsCommutativeMagma_212 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_234 v0 = coe du_setoid_200 (coe d_isMagma_220 (coe v0))
-- Algebra.Structures.IsCommutativeMagma._.sym
d_sym_236 ::
  T_IsCommutativeMagma_212 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_236 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe d_isMagma_220 (coe v0)))
-- Algebra.Structures.IsCommutativeMagma._.trans
d_trans_238 ::
  T_IsCommutativeMagma_212 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_238 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe d_isMagma_220 (coe v0)))
-- Algebra.Structures.IsCommutativeMagma._.∙-cong
d_'8729''45'cong_240 ::
  T_IsCommutativeMagma_212 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_240 v0
  = coe d_'8729''45'cong_186 (coe d_isMagma_220 (coe v0))
-- Algebra.Structures.IsCommutativeMagma._.∙-congʳ
d_'8729''45'cong'691'_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeMagma_212 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_242 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_242 v5
du_'8729''45'cong'691'_242 ::
  T_IsCommutativeMagma_212 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_242 v0
  = coe du_'8729''45'cong'691'_206 (coe d_isMagma_220 (coe v0))
-- Algebra.Structures.IsCommutativeMagma._.∙-congˡ
d_'8729''45'cong'737'_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeMagma_212 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_244 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_244 v5
du_'8729''45'cong'737'_244 ::
  T_IsCommutativeMagma_212 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_244 v0
  = coe du_'8729''45'cong'737'_202 (coe d_isMagma_220 (coe v0))
-- Algebra.Structures.IsIdempotentMagma
d_IsIdempotentMagma_248 a0 a1 a2 a3 a4 = ()
data T_IsIdempotentMagma_248
  = C_IsIdempotentMagma'46'constructor_4535 T_IsMagma_176
                                            (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsIdempotentMagma.isMagma
d_isMagma_256 :: T_IsIdempotentMagma_248 -> T_IsMagma_176
d_isMagma_256 v0
  = case coe v0 of
      C_IsIdempotentMagma'46'constructor_4535 v1 v2 -> coe v1
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentMagma.idem
d_idem_258 :: T_IsIdempotentMagma_248 -> AgdaAny -> AgdaAny
d_idem_258 v0
  = case coe v0 of
      C_IsIdempotentMagma'46'constructor_4535 v1 v2 -> coe v2
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentMagma._.isEquivalence
d_isEquivalence_262 ::
  T_IsIdempotentMagma_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_262 v0
  = coe d_isEquivalence_184 (coe d_isMagma_256 (coe v0))
-- Algebra.Structures.IsIdempotentMagma._.isPartialEquivalence
d_isPartialEquivalence_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsIdempotentMagma_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_264 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_264 v5
du_isPartialEquivalence_264 ::
  T_IsIdempotentMagma_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_264 v0
  = let v1 = d_isMagma_256 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_184 (coe v1)))
-- Algebra.Structures.IsIdempotentMagma._.refl
d_refl_266 :: T_IsIdempotentMagma_248 -> AgdaAny -> AgdaAny
d_refl_266 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe d_isMagma_256 (coe v0)))
-- Algebra.Structures.IsIdempotentMagma._.reflexive
d_reflexive_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsIdempotentMagma_248 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_268 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_268 v5
du_reflexive_268 ::
  T_IsIdempotentMagma_248 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_268 v0
  = let v1 = d_isMagma_256 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_184 (coe v1)) v2)
-- Algebra.Structures.IsIdempotentMagma._.setoid
d_setoid_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsIdempotentMagma_248 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_270 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_270 v5
du_setoid_270 ::
  T_IsIdempotentMagma_248 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_270 v0 = coe du_setoid_200 (coe d_isMagma_256 (coe v0))
-- Algebra.Structures.IsIdempotentMagma._.sym
d_sym_272 ::
  T_IsIdempotentMagma_248 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_272 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe d_isMagma_256 (coe v0)))
-- Algebra.Structures.IsIdempotentMagma._.trans
d_trans_274 ::
  T_IsIdempotentMagma_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_274 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe d_isMagma_256 (coe v0)))
-- Algebra.Structures.IsIdempotentMagma._.∙-cong
d_'8729''45'cong_276 ::
  T_IsIdempotentMagma_248 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_276 v0
  = coe d_'8729''45'cong_186 (coe d_isMagma_256 (coe v0))
-- Algebra.Structures.IsIdempotentMagma._.∙-congʳ
d_'8729''45'cong'691'_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsIdempotentMagma_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_278 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_278 v5
du_'8729''45'cong'691'_278 ::
  T_IsIdempotentMagma_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_278 v0
  = coe du_'8729''45'cong'691'_206 (coe d_isMagma_256 (coe v0))
-- Algebra.Structures.IsIdempotentMagma._.∙-congˡ
d_'8729''45'cong'737'_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsIdempotentMagma_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_280 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_280 v5
du_'8729''45'cong'737'_280 ::
  T_IsIdempotentMagma_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_280 v0
  = coe du_'8729''45'cong'737'_202 (coe d_isMagma_256 (coe v0))
-- Algebra.Structures.IsAlternativeMagma
d_IsAlternativeMagma_284 a0 a1 a2 a3 a4 = ()
data T_IsAlternativeMagma_284
  = C_IsAlternativeMagma'46'constructor_5319 T_IsMagma_176
                                             MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsAlternativeMagma.isMagma
d_isMagma_292 :: T_IsAlternativeMagma_284 -> T_IsMagma_176
d_isMagma_292 v0
  = case coe v0 of
      C_IsAlternativeMagma'46'constructor_5319 v1 v2 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsAlternativeMagma.alter
d_alter_294 ::
  T_IsAlternativeMagma_284 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alter_294 v0
  = case coe v0 of
      C_IsAlternativeMagma'46'constructor_5319 v1 v2 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsAlternativeMagma._.isEquivalence
d_isEquivalence_298 ::
  T_IsAlternativeMagma_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_298 v0
  = coe d_isEquivalence_184 (coe d_isMagma_292 (coe v0))
-- Algebra.Structures.IsAlternativeMagma._.isPartialEquivalence
d_isPartialEquivalence_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_300 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_300 v5
du_isPartialEquivalence_300 ::
  T_IsAlternativeMagma_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_300 v0
  = let v1 = d_isMagma_292 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_184 (coe v1)))
-- Algebra.Structures.IsAlternativeMagma._.refl
d_refl_302 :: T_IsAlternativeMagma_284 -> AgdaAny -> AgdaAny
d_refl_302 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe d_isMagma_292 (coe v0)))
-- Algebra.Structures.IsAlternativeMagma._.reflexive
d_reflexive_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_284 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_304 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_304 v5
du_reflexive_304 ::
  T_IsAlternativeMagma_284 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_304 v0
  = let v1 = d_isMagma_292 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_184 (coe v1)) v2)
-- Algebra.Structures.IsAlternativeMagma._.setoid
d_setoid_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_284 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_306 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_306 v5
du_setoid_306 ::
  T_IsAlternativeMagma_284 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_306 v0 = coe du_setoid_200 (coe d_isMagma_292 (coe v0))
-- Algebra.Structures.IsAlternativeMagma._.sym
d_sym_308 ::
  T_IsAlternativeMagma_284 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_308 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe d_isMagma_292 (coe v0)))
-- Algebra.Structures.IsAlternativeMagma._.trans
d_trans_310 ::
  T_IsAlternativeMagma_284 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_310 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe d_isMagma_292 (coe v0)))
-- Algebra.Structures.IsAlternativeMagma._.∙-cong
d_'8729''45'cong_312 ::
  T_IsAlternativeMagma_284 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_312 v0
  = coe d_'8729''45'cong_186 (coe d_isMagma_292 (coe v0))
-- Algebra.Structures.IsAlternativeMagma._.∙-congʳ
d_'8729''45'cong'691'_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_284 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_314 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_314 v5
du_'8729''45'cong'691'_314 ::
  T_IsAlternativeMagma_284 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_314 v0
  = coe du_'8729''45'cong'691'_206 (coe d_isMagma_292 (coe v0))
-- Algebra.Structures.IsAlternativeMagma._.∙-congˡ
d_'8729''45'cong'737'_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_284 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_316 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_316 v5
du_'8729''45'cong'737'_316 ::
  T_IsAlternativeMagma_284 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_316 v0
  = coe du_'8729''45'cong'737'_202 (coe d_isMagma_292 (coe v0))
-- Algebra.Structures.IsAlternativeMagma.alternativeˡ
d_alternative'737'_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_284 -> AgdaAny -> AgdaAny -> AgdaAny
d_alternative'737'_318 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_alternative'737'_318 v5
du_alternative'737'_318 ::
  T_IsAlternativeMagma_284 -> AgdaAny -> AgdaAny -> AgdaAny
du_alternative'737'_318 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_alter_294 (coe v0))
-- Algebra.Structures.IsAlternativeMagma.alternativeʳ
d_alternative'691'_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsAlternativeMagma_284 -> AgdaAny -> AgdaAny -> AgdaAny
d_alternative'691'_320 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_alternative'691'_320 v5
du_alternative'691'_320 ::
  T_IsAlternativeMagma_284 -> AgdaAny -> AgdaAny -> AgdaAny
du_alternative'691'_320 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_alter_294 (coe v0))
-- Algebra.Structures.IsFlexibleMagma
d_IsFlexibleMagma_324 a0 a1 a2 a3 a4 = ()
data T_IsFlexibleMagma_324
  = C_IsFlexibleMagma'46'constructor_6681 T_IsMagma_176
                                          (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsFlexibleMagma.isMagma
d_isMagma_332 :: T_IsFlexibleMagma_324 -> T_IsMagma_176
d_isMagma_332 v0
  = case coe v0 of
      C_IsFlexibleMagma'46'constructor_6681 v1 v2 -> coe v1
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsFlexibleMagma.flex
d_flex_334 ::
  T_IsFlexibleMagma_324 -> AgdaAny -> AgdaAny -> AgdaAny
d_flex_334 v0
  = case coe v0 of
      C_IsFlexibleMagma'46'constructor_6681 v1 v2 -> coe v2
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsFlexibleMagma._.isEquivalence
d_isEquivalence_338 ::
  T_IsFlexibleMagma_324 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_338 v0
  = coe d_isEquivalence_184 (coe d_isMagma_332 (coe v0))
-- Algebra.Structures.IsFlexibleMagma._.isPartialEquivalence
d_isPartialEquivalence_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsFlexibleMagma_324 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_340 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_340 v5
du_isPartialEquivalence_340 ::
  T_IsFlexibleMagma_324 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_340 v0
  = let v1 = d_isMagma_332 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_184 (coe v1)))
-- Algebra.Structures.IsFlexibleMagma._.refl
d_refl_342 :: T_IsFlexibleMagma_324 -> AgdaAny -> AgdaAny
d_refl_342 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe d_isMagma_332 (coe v0)))
-- Algebra.Structures.IsFlexibleMagma._.reflexive
d_reflexive_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsFlexibleMagma_324 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_344 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_344 v5
du_reflexive_344 ::
  T_IsFlexibleMagma_324 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_344 v0
  = let v1 = d_isMagma_332 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_184 (coe v1)) v2)
-- Algebra.Structures.IsFlexibleMagma._.setoid
d_setoid_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsFlexibleMagma_324 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_346 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_346 v5
du_setoid_346 ::
  T_IsFlexibleMagma_324 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_346 v0 = coe du_setoid_200 (coe d_isMagma_332 (coe v0))
-- Algebra.Structures.IsFlexibleMagma._.sym
d_sym_348 ::
  T_IsFlexibleMagma_324 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_348 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe d_isMagma_332 (coe v0)))
-- Algebra.Structures.IsFlexibleMagma._.trans
d_trans_350 ::
  T_IsFlexibleMagma_324 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_350 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe d_isMagma_332 (coe v0)))
-- Algebra.Structures.IsFlexibleMagma._.∙-cong
d_'8729''45'cong_352 ::
  T_IsFlexibleMagma_324 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_352 v0
  = coe d_'8729''45'cong_186 (coe d_isMagma_332 (coe v0))
-- Algebra.Structures.IsFlexibleMagma._.∙-congʳ
d_'8729''45'cong'691'_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsFlexibleMagma_324 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_354 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_354 v5
du_'8729''45'cong'691'_354 ::
  T_IsFlexibleMagma_324 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_354 v0
  = coe du_'8729''45'cong'691'_206 (coe d_isMagma_332 (coe v0))
-- Algebra.Structures.IsFlexibleMagma._.∙-congˡ
d_'8729''45'cong'737'_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsFlexibleMagma_324 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_356 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_356 v5
du_'8729''45'cong'737'_356 ::
  T_IsFlexibleMagma_324 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_356 v0
  = coe du_'8729''45'cong'737'_202 (coe d_isMagma_332 (coe v0))
-- Algebra.Structures.IsMedialMagma
d_IsMedialMagma_360 a0 a1 a2 a3 a4 = ()
data T_IsMedialMagma_360
  = C_IsMedialMagma'46'constructor_7467 T_IsMagma_176
                                        (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsMedialMagma.isMagma
d_isMagma_368 :: T_IsMedialMagma_360 -> T_IsMagma_176
d_isMagma_368 v0
  = case coe v0 of
      C_IsMedialMagma'46'constructor_7467 v1 v2 -> coe v1
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMedialMagma.medial
d_medial_370 ::
  T_IsMedialMagma_360 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_medial_370 v0
  = case coe v0 of
      C_IsMedialMagma'46'constructor_7467 v1 v2 -> coe v2
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMedialMagma._.isEquivalence
d_isEquivalence_374 ::
  T_IsMedialMagma_360 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_374 v0
  = coe d_isEquivalence_184 (coe d_isMagma_368 (coe v0))
-- Algebra.Structures.IsMedialMagma._.isPartialEquivalence
d_isPartialEquivalence_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMedialMagma_360 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_376 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_376 v5
du_isPartialEquivalence_376 ::
  T_IsMedialMagma_360 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_376 v0
  = let v1 = d_isMagma_368 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_184 (coe v1)))
-- Algebra.Structures.IsMedialMagma._.refl
d_refl_378 :: T_IsMedialMagma_360 -> AgdaAny -> AgdaAny
d_refl_378 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe d_isMagma_368 (coe v0)))
-- Algebra.Structures.IsMedialMagma._.reflexive
d_reflexive_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMedialMagma_360 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_380 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_380 v5
du_reflexive_380 ::
  T_IsMedialMagma_360 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_380 v0
  = let v1 = d_isMagma_368 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_184 (coe v1)) v2)
-- Algebra.Structures.IsMedialMagma._.setoid
d_setoid_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMedialMagma_360 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_382 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_382 v5
du_setoid_382 ::
  T_IsMedialMagma_360 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_382 v0 = coe du_setoid_200 (coe d_isMagma_368 (coe v0))
-- Algebra.Structures.IsMedialMagma._.sym
d_sym_384 ::
  T_IsMedialMagma_360 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_384 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe d_isMagma_368 (coe v0)))
-- Algebra.Structures.IsMedialMagma._.trans
d_trans_386 ::
  T_IsMedialMagma_360 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_386 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe d_isMagma_368 (coe v0)))
-- Algebra.Structures.IsMedialMagma._.∙-cong
d_'8729''45'cong_388 ::
  T_IsMedialMagma_360 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_388 v0
  = coe d_'8729''45'cong_186 (coe d_isMagma_368 (coe v0))
-- Algebra.Structures.IsMedialMagma._.∙-congʳ
d_'8729''45'cong'691'_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMedialMagma_360 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_390 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_390 v5
du_'8729''45'cong'691'_390 ::
  T_IsMedialMagma_360 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_390 v0
  = coe du_'8729''45'cong'691'_206 (coe d_isMagma_368 (coe v0))
-- Algebra.Structures.IsMedialMagma._.∙-congˡ
d_'8729''45'cong'737'_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMedialMagma_360 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_392 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_392 v5
du_'8729''45'cong'737'_392 ::
  T_IsMedialMagma_360 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_392 v0
  = coe du_'8729''45'cong'737'_202 (coe d_isMagma_368 (coe v0))
-- Algebra.Structures.IsSemimedialMagma
d_IsSemimedialMagma_396 a0 a1 a2 a3 a4 = ()
data T_IsSemimedialMagma_396
  = C_IsSemimedialMagma'46'constructor_8257 T_IsMagma_176
                                            MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsSemimedialMagma.isMagma
d_isMagma_404 :: T_IsSemimedialMagma_396 -> T_IsMagma_176
d_isMagma_404 v0
  = case coe v0 of
      C_IsSemimedialMagma'46'constructor_8257 v1 v2 -> coe v1
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemimedialMagma.semiMedial
d_semiMedial_406 ::
  T_IsSemimedialMagma_396 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_semiMedial_406 v0
  = case coe v0 of
      C_IsSemimedialMagma'46'constructor_8257 v1 v2 -> coe v2
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemimedialMagma._.isEquivalence
d_isEquivalence_410 ::
  T_IsSemimedialMagma_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_410 v0
  = coe d_isEquivalence_184 (coe d_isMagma_404 (coe v0))
-- Algebra.Structures.IsSemimedialMagma._.isPartialEquivalence
d_isPartialEquivalence_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_412 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_412 v5
du_isPartialEquivalence_412 ::
  T_IsSemimedialMagma_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_412 v0
  = let v1 = d_isMagma_404 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_184 (coe v1)))
-- Algebra.Structures.IsSemimedialMagma._.refl
d_refl_414 :: T_IsSemimedialMagma_396 -> AgdaAny -> AgdaAny
d_refl_414 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe d_isMagma_404 (coe v0)))
-- Algebra.Structures.IsSemimedialMagma._.reflexive
d_reflexive_416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_396 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_416 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_416 v5
du_reflexive_416 ::
  T_IsSemimedialMagma_396 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_416 v0
  = let v1 = d_isMagma_404 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_184 (coe v1)) v2)
-- Algebra.Structures.IsSemimedialMagma._.setoid
d_setoid_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_396 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_418 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_418 v5
du_setoid_418 ::
  T_IsSemimedialMagma_396 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_418 v0 = coe du_setoid_200 (coe d_isMagma_404 (coe v0))
-- Algebra.Structures.IsSemimedialMagma._.sym
d_sym_420 ::
  T_IsSemimedialMagma_396 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_420 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe d_isMagma_404 (coe v0)))
-- Algebra.Structures.IsSemimedialMagma._.trans
d_trans_422 ::
  T_IsSemimedialMagma_396 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_422 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe d_isMagma_404 (coe v0)))
-- Algebra.Structures.IsSemimedialMagma._.∙-cong
d_'8729''45'cong_424 ::
  T_IsSemimedialMagma_396 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_424 v0
  = coe d_'8729''45'cong_186 (coe d_isMagma_404 (coe v0))
-- Algebra.Structures.IsSemimedialMagma._.∙-congʳ
d_'8729''45'cong'691'_426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_396 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_426 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_426 v5
du_'8729''45'cong'691'_426 ::
  T_IsSemimedialMagma_396 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_426 v0
  = coe du_'8729''45'cong'691'_206 (coe d_isMagma_404 (coe v0))
-- Algebra.Structures.IsSemimedialMagma._.∙-congˡ
d_'8729''45'cong'737'_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_396 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_428 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_428 v5
du_'8729''45'cong'737'_428 ::
  T_IsSemimedialMagma_396 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_428 v0
  = coe du_'8729''45'cong'737'_202 (coe d_isMagma_404 (coe v0))
-- Algebra.Structures.IsSemimedialMagma.semimedialˡ
d_semimedial'737'_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_396 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_semimedial'737'_430 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_semimedial'737'_430 v5
du_semimedial'737'_430 ::
  T_IsSemimedialMagma_396 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_semimedial'737'_430 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_semiMedial_406 (coe v0))
-- Algebra.Structures.IsSemimedialMagma.semimedialʳ
d_semimedial'691'_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemimedialMagma_396 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_semimedial'691'_432 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_semimedial'691'_432 v5
du_semimedial'691'_432 ::
  T_IsSemimedialMagma_396 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_semimedial'691'_432 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_semiMedial_406 (coe v0))
-- Algebra.Structures.IsSelectiveMagma
d_IsSelectiveMagma_436 a0 a1 a2 a3 a4 = ()
data T_IsSelectiveMagma_436
  = C_IsSelectiveMagma'46'constructor_9631 T_IsMagma_176
                                           (AgdaAny ->
                                            AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Algebra.Structures.IsSelectiveMagma.isMagma
d_isMagma_444 :: T_IsSelectiveMagma_436 -> T_IsMagma_176
d_isMagma_444 v0
  = case coe v0 of
      C_IsSelectiveMagma'46'constructor_9631 v1 v2 -> coe v1
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSelectiveMagma.sel
d_sel_446 ::
  T_IsSelectiveMagma_436 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_446 v0
  = case coe v0 of
      C_IsSelectiveMagma'46'constructor_9631 v1 v2 -> coe v2
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSelectiveMagma._.isEquivalence
d_isEquivalence_450 ::
  T_IsSelectiveMagma_436 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_450 v0
  = coe d_isEquivalence_184 (coe d_isMagma_444 (coe v0))
-- Algebra.Structures.IsSelectiveMagma._.isPartialEquivalence
d_isPartialEquivalence_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSelectiveMagma_436 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_452 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_452 v5
du_isPartialEquivalence_452 ::
  T_IsSelectiveMagma_436 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_452 v0
  = let v1 = d_isMagma_444 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_184 (coe v1)))
-- Algebra.Structures.IsSelectiveMagma._.refl
d_refl_454 :: T_IsSelectiveMagma_436 -> AgdaAny -> AgdaAny
d_refl_454 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe d_isMagma_444 (coe v0)))
-- Algebra.Structures.IsSelectiveMagma._.reflexive
d_reflexive_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSelectiveMagma_436 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_456 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_456 v5
du_reflexive_456 ::
  T_IsSelectiveMagma_436 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_456 v0
  = let v1 = d_isMagma_444 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_184 (coe v1)) v2)
-- Algebra.Structures.IsSelectiveMagma._.setoid
d_setoid_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSelectiveMagma_436 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_458 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_458 v5
du_setoid_458 ::
  T_IsSelectiveMagma_436 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_458 v0 = coe du_setoid_200 (coe d_isMagma_444 (coe v0))
-- Algebra.Structures.IsSelectiveMagma._.sym
d_sym_460 ::
  T_IsSelectiveMagma_436 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_460 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe d_isMagma_444 (coe v0)))
-- Algebra.Structures.IsSelectiveMagma._.trans
d_trans_462 ::
  T_IsSelectiveMagma_436 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_462 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe d_isMagma_444 (coe v0)))
-- Algebra.Structures.IsSelectiveMagma._.∙-cong
d_'8729''45'cong_464 ::
  T_IsSelectiveMagma_436 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_464 v0
  = coe d_'8729''45'cong_186 (coe d_isMagma_444 (coe v0))
-- Algebra.Structures.IsSelectiveMagma._.∙-congʳ
d_'8729''45'cong'691'_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSelectiveMagma_436 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_466 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_466 v5
du_'8729''45'cong'691'_466 ::
  T_IsSelectiveMagma_436 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_466 v0
  = coe du_'8729''45'cong'691'_206 (coe d_isMagma_444 (coe v0))
-- Algebra.Structures.IsSelectiveMagma._.∙-congˡ
d_'8729''45'cong'737'_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSelectiveMagma_436 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_468 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_468 v5
du_'8729''45'cong'737'_468 ::
  T_IsSelectiveMagma_436 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_468 v0
  = coe du_'8729''45'cong'737'_202 (coe d_isMagma_444 (coe v0))
-- Algebra.Structures.IsSemigroup
d_IsSemigroup_472 a0 a1 a2 a3 a4 = ()
data T_IsSemigroup_472
  = C_IsSemigroup'46'constructor_10417 T_IsMagma_176
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsSemigroup.isMagma
d_isMagma_480 :: T_IsSemigroup_472 -> T_IsMagma_176
d_isMagma_480 v0
  = case coe v0 of
      C_IsSemigroup'46'constructor_10417 v1 v2 -> coe v1
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemigroup.assoc
d_assoc_482 ::
  T_IsSemigroup_472 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_482 v0
  = case coe v0 of
      C_IsSemigroup'46'constructor_10417 v1 v2 -> coe v2
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemigroup._.isEquivalence
d_isEquivalence_486 ::
  T_IsSemigroup_472 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_486 v0
  = coe d_isEquivalence_184 (coe d_isMagma_480 (coe v0))
-- Algebra.Structures.IsSemigroup._.isPartialEquivalence
d_isPartialEquivalence_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemigroup_472 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_488 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_488 v5
du_isPartialEquivalence_488 ::
  T_IsSemigroup_472 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_488 v0
  = let v1 = d_isMagma_480 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_184 (coe v1)))
-- Algebra.Structures.IsSemigroup._.refl
d_refl_490 :: T_IsSemigroup_472 -> AgdaAny -> AgdaAny
d_refl_490 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe d_isMagma_480 (coe v0)))
-- Algebra.Structures.IsSemigroup._.reflexive
d_reflexive_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemigroup_472 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_492 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_492 v5
du_reflexive_492 ::
  T_IsSemigroup_472 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_492 v0
  = let v1 = d_isMagma_480 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_184 (coe v1)) v2)
-- Algebra.Structures.IsSemigroup._.setoid
d_setoid_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemigroup_472 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_494 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_494 v5
du_setoid_494 ::
  T_IsSemigroup_472 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_494 v0 = coe du_setoid_200 (coe d_isMagma_480 (coe v0))
-- Algebra.Structures.IsSemigroup._.sym
d_sym_496 ::
  T_IsSemigroup_472 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_496 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe d_isMagma_480 (coe v0)))
-- Algebra.Structures.IsSemigroup._.trans
d_trans_498 ::
  T_IsSemigroup_472 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_498 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe d_isMagma_480 (coe v0)))
-- Algebra.Structures.IsSemigroup._.∙-cong
d_'8729''45'cong_500 ::
  T_IsSemigroup_472 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_500 v0
  = coe d_'8729''45'cong_186 (coe d_isMagma_480 (coe v0))
-- Algebra.Structures.IsSemigroup._.∙-congʳ
d_'8729''45'cong'691'_502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemigroup_472 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_502 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_502 v5
du_'8729''45'cong'691'_502 ::
  T_IsSemigroup_472 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_502 v0
  = coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v0))
-- Algebra.Structures.IsSemigroup._.∙-congˡ
d_'8729''45'cong'737'_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemigroup_472 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_504 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_504 v5
du_'8729''45'cong'737'_504 ::
  T_IsSemigroup_472 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_504 v0
  = coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v0))
-- Algebra.Structures.IsBand
d_IsBand_508 a0 a1 a2 a3 a4 = ()
data T_IsBand_508
  = C_IsBand'46'constructor_11205 T_IsSemigroup_472
                                  (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsBand.isSemigroup
d_isSemigroup_516 :: T_IsBand_508 -> T_IsSemigroup_472
d_isSemigroup_516 v0
  = case coe v0 of
      C_IsBand'46'constructor_11205 v1 v2 -> coe v1
      _                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsBand.idem
d_idem_518 :: T_IsBand_508 -> AgdaAny -> AgdaAny
d_idem_518 v0
  = case coe v0 of
      C_IsBand'46'constructor_11205 v1 v2 -> coe v2
      _                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsBand._.assoc
d_assoc_522 ::
  T_IsBand_508 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_522 v0 = coe d_assoc_482 (coe d_isSemigroup_516 (coe v0))
-- Algebra.Structures.IsBand._.isEquivalence
d_isEquivalence_524 ::
  T_IsBand_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_524 v0
  = coe
      d_isEquivalence_184
      (coe d_isMagma_480 (coe d_isSemigroup_516 (coe v0)))
-- Algebra.Structures.IsBand._.isMagma
d_isMagma_526 :: T_IsBand_508 -> T_IsMagma_176
d_isMagma_526 v0
  = coe d_isMagma_480 (coe d_isSemigroup_516 (coe v0))
-- Algebra.Structures.IsBand._.isPartialEquivalence
d_isPartialEquivalence_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsBand_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_528 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_528 v5
du_isPartialEquivalence_528 ::
  T_IsBand_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_528 v0
  = let v1 = d_isSemigroup_516 (coe v0) in
    coe
      (let v2 = d_isMagma_480 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe d_isEquivalence_184 (coe v2))))
-- Algebra.Structures.IsBand._.refl
d_refl_530 :: T_IsBand_508 -> AgdaAny -> AgdaAny
d_refl_530 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe d_isMagma_480 (coe d_isSemigroup_516 (coe v0))))
-- Algebra.Structures.IsBand._.reflexive
d_reflexive_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsBand_508 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_532 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_532 v5
du_reflexive_532 ::
  T_IsBand_508 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_532 v0
  = let v1 = d_isSemigroup_516 (coe v0) in
    coe
      (let v2 = d_isMagma_480 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe d_isEquivalence_184 (coe v2)) v3))
-- Algebra.Structures.IsBand._.setoid
d_setoid_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsBand_508 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_534 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_534 v5
du_setoid_534 ::
  T_IsBand_508 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_534 v0
  = let v1 = d_isSemigroup_516 (coe v0) in
    coe (coe du_setoid_200 (coe d_isMagma_480 (coe v1)))
-- Algebra.Structures.IsBand._.sym
d_sym_536 ::
  T_IsBand_508 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_536 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe d_isMagma_480 (coe d_isSemigroup_516 (coe v0))))
-- Algebra.Structures.IsBand._.trans
d_trans_538 ::
  T_IsBand_508 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_538 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe d_isMagma_480 (coe d_isSemigroup_516 (coe v0))))
-- Algebra.Structures.IsBand._.∙-cong
d_'8729''45'cong_540 ::
  T_IsBand_508 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_540 v0
  = coe
      d_'8729''45'cong_186
      (coe d_isMagma_480 (coe d_isSemigroup_516 (coe v0)))
-- Algebra.Structures.IsBand._.∙-congʳ
d_'8729''45'cong'691'_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsBand_508 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_542 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_542 v5
du_'8729''45'cong'691'_542 ::
  T_IsBand_508 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_542 v0
  = let v1 = d_isSemigroup_516 (coe v0) in
    coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v1)))
-- Algebra.Structures.IsBand._.∙-congˡ
d_'8729''45'cong'737'_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsBand_508 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_544 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_544 v5
du_'8729''45'cong'737'_544 ::
  T_IsBand_508 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_544 v0
  = let v1 = d_isSemigroup_516 (coe v0) in
    coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v1)))
-- Algebra.Structures.IsCommutativeSemigroup
d_IsCommutativeSemigroup_548 a0 a1 a2 a3 a4 = ()
data T_IsCommutativeSemigroup_548
  = C_IsCommutativeSemigroup'46'constructor_12093 T_IsSemigroup_472
                                                  (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_556 ::
  T_IsCommutativeSemigroup_548 -> T_IsSemigroup_472
d_isSemigroup_556 v0
  = case coe v0 of
      C_IsCommutativeSemigroup'46'constructor_12093 v1 v2 -> coe v1
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemigroup.comm
d_comm_558 ::
  T_IsCommutativeSemigroup_548 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_558 v0
  = case coe v0 of
      C_IsCommutativeSemigroup'46'constructor_12093 v1 v2 -> coe v2
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemigroup._.assoc
d_assoc_562 ::
  T_IsCommutativeSemigroup_548 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_562 v0 = coe d_assoc_482 (coe d_isSemigroup_556 (coe v0))
-- Algebra.Structures.IsCommutativeSemigroup._.isEquivalence
d_isEquivalence_564 ::
  T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_564 v0
  = coe
      d_isEquivalence_184
      (coe d_isMagma_480 (coe d_isSemigroup_556 (coe v0)))
-- Algebra.Structures.IsCommutativeSemigroup._.isMagma
d_isMagma_566 :: T_IsCommutativeSemigroup_548 -> T_IsMagma_176
d_isMagma_566 v0
  = coe d_isMagma_480 (coe d_isSemigroup_556 (coe v0))
-- Algebra.Structures.IsCommutativeSemigroup._.isPartialEquivalence
d_isPartialEquivalence_568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_568 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_568 v5
du_isPartialEquivalence_568 ::
  T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_568 v0
  = let v1 = d_isSemigroup_556 (coe v0) in
    coe
      (let v2 = d_isMagma_480 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe d_isEquivalence_184 (coe v2))))
-- Algebra.Structures.IsCommutativeSemigroup._.refl
d_refl_570 :: T_IsCommutativeSemigroup_548 -> AgdaAny -> AgdaAny
d_refl_570 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe d_isMagma_480 (coe d_isSemigroup_556 (coe v0))))
-- Algebra.Structures.IsCommutativeSemigroup._.reflexive
d_reflexive_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_548 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_572 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_572 v5
du_reflexive_572 ::
  T_IsCommutativeSemigroup_548 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_572 v0
  = let v1 = d_isSemigroup_556 (coe v0) in
    coe
      (let v2 = d_isMagma_480 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe d_isEquivalence_184 (coe v2)) v3))
-- Algebra.Structures.IsCommutativeSemigroup._.setoid
d_setoid_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_574 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_574 v5
du_setoid_574 ::
  T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_574 v0
  = let v1 = d_isSemigroup_556 (coe v0) in
    coe (coe du_setoid_200 (coe d_isMagma_480 (coe v1)))
-- Algebra.Structures.IsCommutativeSemigroup._.sym
d_sym_576 ::
  T_IsCommutativeSemigroup_548 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_576 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe d_isMagma_480 (coe d_isSemigroup_556 (coe v0))))
-- Algebra.Structures.IsCommutativeSemigroup._.trans
d_trans_578 ::
  T_IsCommutativeSemigroup_548 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_578 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe d_isMagma_480 (coe d_isSemigroup_556 (coe v0))))
-- Algebra.Structures.IsCommutativeSemigroup._.∙-cong
d_'8729''45'cong_580 ::
  T_IsCommutativeSemigroup_548 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_580 v0
  = coe
      d_'8729''45'cong_186
      (coe d_isMagma_480 (coe d_isSemigroup_556 (coe v0)))
-- Algebra.Structures.IsCommutativeSemigroup._.∙-congʳ
d_'8729''45'cong'691'_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_548 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_582 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_582 v5
du_'8729''45'cong'691'_582 ::
  T_IsCommutativeSemigroup_548 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_582 v0
  = let v1 = d_isSemigroup_556 (coe v0) in
    coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v1)))
-- Algebra.Structures.IsCommutativeSemigroup._.∙-congˡ
d_'8729''45'cong'737'_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_548 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_584 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_584 v5
du_'8729''45'cong'737'_584 ::
  T_IsCommutativeSemigroup_548 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_584 v0
  = let v1 = d_isSemigroup_556 (coe v0) in
    coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v1)))
-- Algebra.Structures.IsCommutativeSemigroup.isCommutativeMagma
d_isCommutativeMagma_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeSemigroup_548 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_586 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_586 v5
du_isCommutativeMagma_586 ::
  T_IsCommutativeSemigroup_548 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_586 v0
  = coe
      C_IsCommutativeMagma'46'constructor_3749
      (coe d_isMagma_480 (coe d_isSemigroup_556 (coe v0)))
      (coe d_comm_558 (coe v0))
-- Algebra.Structures.IsCommutativeBand
d_IsCommutativeBand_590 a0 a1 a2 a3 a4 = ()
data T_IsCommutativeBand_590
  = C_IsCommutativeBand'46'constructor_13109 T_IsBand_508
                                             (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeBand.isBand
d_isBand_598 :: T_IsCommutativeBand_590 -> T_IsBand_508
d_isBand_598 v0
  = case coe v0 of
      C_IsCommutativeBand'46'constructor_13109 v1 v2 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeBand.comm
d_comm_600 ::
  T_IsCommutativeBand_590 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_600 v0
  = case coe v0 of
      C_IsCommutativeBand'46'constructor_13109 v1 v2 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeBand._.assoc
d_assoc_604 ::
  T_IsCommutativeBand_590 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_604 v0
  = coe
      d_assoc_482 (coe d_isSemigroup_516 (coe d_isBand_598 (coe v0)))
-- Algebra.Structures.IsCommutativeBand._.idem
d_idem_606 :: T_IsCommutativeBand_590 -> AgdaAny -> AgdaAny
d_idem_606 v0 = coe d_idem_518 (coe d_isBand_598 (coe v0))
-- Algebra.Structures.IsCommutativeBand._.isEquivalence
d_isEquivalence_608 ::
  T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_608 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480 (coe d_isSemigroup_516 (coe d_isBand_598 (coe v0))))
-- Algebra.Structures.IsCommutativeBand._.isMagma
d_isMagma_610 :: T_IsCommutativeBand_590 -> T_IsMagma_176
d_isMagma_610 v0
  = coe
      d_isMagma_480 (coe d_isSemigroup_516 (coe d_isBand_598 (coe v0)))
-- Algebra.Structures.IsCommutativeBand._.isPartialEquivalence
d_isPartialEquivalence_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_612 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_612 v5
du_isPartialEquivalence_612 ::
  T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_612 v0
  = let v1 = d_isBand_598 (coe v0) in
    coe
      (let v2 = d_isSemigroup_516 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.IsCommutativeBand._.isSemigroup
d_isSemigroup_614 :: T_IsCommutativeBand_590 -> T_IsSemigroup_472
d_isSemigroup_614 v0
  = coe d_isSemigroup_516 (coe d_isBand_598 (coe v0))
-- Algebra.Structures.IsCommutativeBand._.refl
d_refl_616 :: T_IsCommutativeBand_590 -> AgdaAny -> AgdaAny
d_refl_616 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480 (coe d_isSemigroup_516 (coe d_isBand_598 (coe v0)))))
-- Algebra.Structures.IsCommutativeBand._.reflexive
d_reflexive_618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_590 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_618 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_618 v5
du_reflexive_618 ::
  T_IsCommutativeBand_590 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_618 v0
  = let v1 = d_isBand_598 (coe v0) in
    coe
      (let v2 = d_isSemigroup_516 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_184 (coe v3)) v4)))
-- Algebra.Structures.IsCommutativeBand._.setoid
d_setoid_620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_620 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_620 v5
du_setoid_620 ::
  T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_620 v0
  = let v1 = d_isBand_598 (coe v0) in
    coe
      (let v2 = d_isSemigroup_516 (coe v1) in
       coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsCommutativeBand._.sym
d_sym_622 ::
  T_IsCommutativeBand_590 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_622 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480 (coe d_isSemigroup_516 (coe d_isBand_598 (coe v0)))))
-- Algebra.Structures.IsCommutativeBand._.trans
d_trans_624 ::
  T_IsCommutativeBand_590 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_624 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480 (coe d_isSemigroup_516 (coe d_isBand_598 (coe v0)))))
-- Algebra.Structures.IsCommutativeBand._.∙-cong
d_'8729''45'cong_626 ::
  T_IsCommutativeBand_590 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_626 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480 (coe d_isSemigroup_516 (coe d_isBand_598 (coe v0))))
-- Algebra.Structures.IsCommutativeBand._.∙-congʳ
d_'8729''45'cong'691'_628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_590 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_628 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_628 v5
du_'8729''45'cong'691'_628 ::
  T_IsCommutativeBand_590 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_628 v0
  = let v1 = d_isBand_598 (coe v0) in
    coe
      (let v2 = d_isSemigroup_516 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsCommutativeBand._.∙-congˡ
d_'8729''45'cong'737'_630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_590 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_630 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_630 v5
du_'8729''45'cong'737'_630 ::
  T_IsCommutativeBand_590 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_630 v0
  = let v1 = d_isBand_598 (coe v0) in
    coe
      (let v2 = d_isSemigroup_516 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsCommutativeBand.isCommutativeSemigroup
d_isCommutativeSemigroup_632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_590 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_632 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_632 v5
du_isCommutativeSemigroup_632 ::
  T_IsCommutativeBand_590 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_632 v0
  = coe
      C_IsCommutativeSemigroup'46'constructor_12093
      (coe d_isSemigroup_516 (coe d_isBand_598 (coe v0)))
      (coe d_comm_600 (coe v0))
-- Algebra.Structures.IsCommutativeBand._.isCommutativeMagma
d_isCommutativeMagma_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCommutativeBand_590 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_636 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_636 v5
du_isCommutativeMagma_636 ::
  T_IsCommutativeBand_590 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_636 v0
  = coe
      du_isCommutativeMagma_586
      (coe du_isCommutativeSemigroup_632 (coe v0))
-- Algebra.Structures.IsUnitalMagma
d_IsUnitalMagma_642 a0 a1 a2 a3 a4 a5 = ()
data T_IsUnitalMagma_642
  = C_IsUnitalMagma'46'constructor_14317 T_IsMagma_176
                                         MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsUnitalMagma.isMagma
d_isMagma_652 :: T_IsUnitalMagma_642 -> T_IsMagma_176
d_isMagma_652 v0
  = case coe v0 of
      C_IsUnitalMagma'46'constructor_14317 v1 v2 -> coe v1
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsUnitalMagma.identity
d_identity_654 ::
  T_IsUnitalMagma_642 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_654 v0
  = case coe v0 of
      C_IsUnitalMagma'46'constructor_14317 v1 v2 -> coe v2
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsUnitalMagma._.isEquivalence
d_isEquivalence_658 ::
  T_IsUnitalMagma_642 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_658 v0
  = coe d_isEquivalence_184 (coe d_isMagma_652 (coe v0))
-- Algebra.Structures.IsUnitalMagma._.isPartialEquivalence
d_isPartialEquivalence_660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsUnitalMagma_642 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_660 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_660 v6
du_isPartialEquivalence_660 ::
  T_IsUnitalMagma_642 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_660 v0
  = let v1 = d_isMagma_652 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_184 (coe v1)))
-- Algebra.Structures.IsUnitalMagma._.refl
d_refl_662 :: T_IsUnitalMagma_642 -> AgdaAny -> AgdaAny
d_refl_662 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe d_isMagma_652 (coe v0)))
-- Algebra.Structures.IsUnitalMagma._.reflexive
d_reflexive_664 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsUnitalMagma_642 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_664 v6
du_reflexive_664 ::
  T_IsUnitalMagma_642 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_664 v0
  = let v1 = d_isMagma_652 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_184 (coe v1)) v2)
-- Algebra.Structures.IsUnitalMagma._.setoid
d_setoid_666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsUnitalMagma_642 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_666 v6
du_setoid_666 ::
  T_IsUnitalMagma_642 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_666 v0 = coe du_setoid_200 (coe d_isMagma_652 (coe v0))
-- Algebra.Structures.IsUnitalMagma._.sym
d_sym_668 ::
  T_IsUnitalMagma_642 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_668 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe d_isMagma_652 (coe v0)))
-- Algebra.Structures.IsUnitalMagma._.trans
d_trans_670 ::
  T_IsUnitalMagma_642 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_670 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe d_isMagma_652 (coe v0)))
-- Algebra.Structures.IsUnitalMagma._.∙-cong
d_'8729''45'cong_672 ::
  T_IsUnitalMagma_642 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_672 v0
  = coe d_'8729''45'cong_186 (coe d_isMagma_652 (coe v0))
-- Algebra.Structures.IsUnitalMagma._.∙-congʳ
d_'8729''45'cong'691'_674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsUnitalMagma_642 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_674 v6
du_'8729''45'cong'691'_674 ::
  T_IsUnitalMagma_642 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_674 v0
  = coe du_'8729''45'cong'691'_206 (coe d_isMagma_652 (coe v0))
-- Algebra.Structures.IsUnitalMagma._.∙-congˡ
d_'8729''45'cong'737'_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsUnitalMagma_642 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_676 v6
du_'8729''45'cong'737'_676 ::
  T_IsUnitalMagma_642 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_676 v0
  = coe du_'8729''45'cong'737'_202 (coe d_isMagma_652 (coe v0))
-- Algebra.Structures.IsUnitalMagma.identityˡ
d_identity'737'_678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsUnitalMagma_642 -> AgdaAny -> AgdaAny
d_identity'737'_678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_678 v6
du_identity'737'_678 :: T_IsUnitalMagma_642 -> AgdaAny -> AgdaAny
du_identity'737'_678 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_identity_654 (coe v0))
-- Algebra.Structures.IsUnitalMagma.identityʳ
d_identity'691'_680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsUnitalMagma_642 -> AgdaAny -> AgdaAny
d_identity'691'_680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_680 v6
du_identity'691'_680 :: T_IsUnitalMagma_642 -> AgdaAny -> AgdaAny
du_identity'691'_680 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_identity_654 (coe v0))
-- Algebra.Structures.IsMonoid
d_IsMonoid_686 a0 a1 a2 a3 a4 a5 = ()
data T_IsMonoid_686
  = C_IsMonoid'46'constructor_15873 T_IsSemigroup_472
                                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsMonoid.isSemigroup
d_isSemigroup_696 :: T_IsMonoid_686 -> T_IsSemigroup_472
d_isSemigroup_696 v0
  = case coe v0 of
      C_IsMonoid'46'constructor_15873 v1 v2 -> coe v1
      _                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMonoid.identity
d_identity_698 ::
  T_IsMonoid_686 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_698 v0
  = case coe v0 of
      C_IsMonoid'46'constructor_15873 v1 v2 -> coe v2
      _                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMonoid._.assoc
d_assoc_702 ::
  T_IsMonoid_686 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_702 v0 = coe d_assoc_482 (coe d_isSemigroup_696 (coe v0))
-- Algebra.Structures.IsMonoid._.isEquivalence
d_isEquivalence_704 ::
  T_IsMonoid_686 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_704 v0
  = coe
      d_isEquivalence_184
      (coe d_isMagma_480 (coe d_isSemigroup_696 (coe v0)))
-- Algebra.Structures.IsMonoid._.isMagma
d_isMagma_706 :: T_IsMonoid_686 -> T_IsMagma_176
d_isMagma_706 v0
  = coe d_isMagma_480 (coe d_isSemigroup_696 (coe v0))
-- Algebra.Structures.IsMonoid._.isPartialEquivalence
d_isPartialEquivalence_708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMonoid_686 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_708 v6
du_isPartialEquivalence_708 ::
  T_IsMonoid_686 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_708 v0
  = let v1 = d_isSemigroup_696 (coe v0) in
    coe
      (let v2 = d_isMagma_480 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe d_isEquivalence_184 (coe v2))))
-- Algebra.Structures.IsMonoid._.refl
d_refl_710 :: T_IsMonoid_686 -> AgdaAny -> AgdaAny
d_refl_710 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe d_isMagma_480 (coe d_isSemigroup_696 (coe v0))))
-- Algebra.Structures.IsMonoid._.reflexive
d_reflexive_712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMonoid_686 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_712 v6
du_reflexive_712 ::
  T_IsMonoid_686 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_712 v0
  = let v1 = d_isSemigroup_696 (coe v0) in
    coe
      (let v2 = d_isMagma_480 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe d_isEquivalence_184 (coe v2)) v3))
-- Algebra.Structures.IsMonoid._.setoid
d_setoid_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMonoid_686 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_714 v6
du_setoid_714 ::
  T_IsMonoid_686 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_714 v0
  = let v1 = d_isSemigroup_696 (coe v0) in
    coe (coe du_setoid_200 (coe d_isMagma_480 (coe v1)))
-- Algebra.Structures.IsMonoid._.sym
d_sym_716 ::
  T_IsMonoid_686 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_716 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe d_isMagma_480 (coe d_isSemigroup_696 (coe v0))))
-- Algebra.Structures.IsMonoid._.trans
d_trans_718 ::
  T_IsMonoid_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_718 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe d_isMagma_480 (coe d_isSemigroup_696 (coe v0))))
-- Algebra.Structures.IsMonoid._.∙-cong
d_'8729''45'cong_720 ::
  T_IsMonoid_686 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_720 v0
  = coe
      d_'8729''45'cong_186
      (coe d_isMagma_480 (coe d_isSemigroup_696 (coe v0)))
-- Algebra.Structures.IsMonoid._.∙-congʳ
d_'8729''45'cong'691'_722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMonoid_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_722 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_722 v6
du_'8729''45'cong'691'_722 ::
  T_IsMonoid_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_722 v0
  = let v1 = d_isSemigroup_696 (coe v0) in
    coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v1)))
-- Algebra.Structures.IsMonoid._.∙-congˡ
d_'8729''45'cong'737'_724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMonoid_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_724 v6
du_'8729''45'cong'737'_724 ::
  T_IsMonoid_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_724 v0
  = let v1 = d_isSemigroup_696 (coe v0) in
    coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v1)))
-- Algebra.Structures.IsMonoid.identityˡ
d_identity'737'_726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMonoid_686 -> AgdaAny -> AgdaAny
d_identity'737'_726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_726 v6
du_identity'737'_726 :: T_IsMonoid_686 -> AgdaAny -> AgdaAny
du_identity'737'_726 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_identity_698 (coe v0))
-- Algebra.Structures.IsMonoid.identityʳ
d_identity'691'_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMonoid_686 -> AgdaAny -> AgdaAny
d_identity'691'_728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_728 v6
du_identity'691'_728 :: T_IsMonoid_686 -> AgdaAny -> AgdaAny
du_identity'691'_728 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_identity_698 (coe v0))
-- Algebra.Structures.IsMonoid.isUnitalMagma
d_isUnitalMagma_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMonoid_686 -> T_IsUnitalMagma_642
d_isUnitalMagma_730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isUnitalMagma_730 v6
du_isUnitalMagma_730 :: T_IsMonoid_686 -> T_IsUnitalMagma_642
du_isUnitalMagma_730 v0
  = coe
      C_IsUnitalMagma'46'constructor_14317
      (coe d_isMagma_480 (coe d_isSemigroup_696 (coe v0)))
      (coe d_identity_698 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid
d_IsCommutativeMonoid_736 a0 a1 a2 a3 a4 a5 = ()
data T_IsCommutativeMonoid_736
  = C_IsCommutativeMonoid'46'constructor_17695 T_IsMonoid_686
                                               (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeMonoid.isMonoid
d_isMonoid_746 :: T_IsCommutativeMonoid_736 -> T_IsMonoid_686
d_isMonoid_746 v0
  = case coe v0 of
      C_IsCommutativeMonoid'46'constructor_17695 v1 v2 -> coe v1
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeMonoid.comm
d_comm_748 ::
  T_IsCommutativeMonoid_736 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_748 v0
  = case coe v0 of
      C_IsCommutativeMonoid'46'constructor_17695 v1 v2 -> coe v2
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeMonoid._.assoc
d_assoc_752 ::
  T_IsCommutativeMonoid_736 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_752 v0
  = coe
      d_assoc_482 (coe d_isSemigroup_696 (coe d_isMonoid_746 (coe v0)))
-- Algebra.Structures.IsCommutativeMonoid._.identity
d_identity_754 ::
  T_IsCommutativeMonoid_736 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_754 v0
  = coe d_identity_698 (coe d_isMonoid_746 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.identityʳ
d_identity'691'_756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeMonoid_736 -> AgdaAny -> AgdaAny
d_identity'691'_756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_756 v6
du_identity'691'_756 ::
  T_IsCommutativeMonoid_736 -> AgdaAny -> AgdaAny
du_identity'691'_756 v0
  = coe du_identity'691'_728 (coe d_isMonoid_746 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.identityˡ
d_identity'737'_758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeMonoid_736 -> AgdaAny -> AgdaAny
d_identity'737'_758 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_758 v6
du_identity'737'_758 ::
  T_IsCommutativeMonoid_736 -> AgdaAny -> AgdaAny
du_identity'737'_758 v0
  = coe du_identity'737'_726 (coe d_isMonoid_746 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.isEquivalence
d_isEquivalence_760 ::
  T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_760 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe d_isSemigroup_696 (coe d_isMonoid_746 (coe v0))))
-- Algebra.Structures.IsCommutativeMonoid._.isMagma
d_isMagma_762 :: T_IsCommutativeMonoid_736 -> T_IsMagma_176
d_isMagma_762 v0
  = coe
      d_isMagma_480 (coe d_isSemigroup_696 (coe d_isMonoid_746 (coe v0)))
-- Algebra.Structures.IsCommutativeMonoid._.isPartialEquivalence
d_isPartialEquivalence_764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_764 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_764 v6
du_isPartialEquivalence_764 ::
  T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_764 v0
  = let v1 = d_isMonoid_746 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.IsCommutativeMonoid._.isSemigroup
d_isSemigroup_766 :: T_IsCommutativeMonoid_736 -> T_IsSemigroup_472
d_isSemigroup_766 v0
  = coe d_isSemigroup_696 (coe d_isMonoid_746 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.isUnitalMagma
d_isUnitalMagma_768 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeMonoid_736 -> T_IsUnitalMagma_642
d_isUnitalMagma_768 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isUnitalMagma_768 v6
du_isUnitalMagma_768 ::
  T_IsCommutativeMonoid_736 -> T_IsUnitalMagma_642
du_isUnitalMagma_768 v0
  = coe du_isUnitalMagma_730 (coe d_isMonoid_746 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.refl
d_refl_770 :: T_IsCommutativeMonoid_736 -> AgdaAny -> AgdaAny
d_refl_770 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_isMonoid_746 (coe v0)))))
-- Algebra.Structures.IsCommutativeMonoid._.reflexive
d_reflexive_772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_736 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_772 v6
du_reflexive_772 ::
  T_IsCommutativeMonoid_736 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_772 v0
  = let v1 = d_isMonoid_746 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_184 (coe v3)) v4)))
-- Algebra.Structures.IsCommutativeMonoid._.setoid
d_setoid_774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_774 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_774 v6
du_setoid_774 ::
  T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_774 v0
  = let v1 = d_isMonoid_746 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsCommutativeMonoid._.sym
d_sym_776 ::
  T_IsCommutativeMonoid_736 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_776 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_isMonoid_746 (coe v0)))))
-- Algebra.Structures.IsCommutativeMonoid._.trans
d_trans_778 ::
  T_IsCommutativeMonoid_736 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_778 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_isMonoid_746 (coe v0)))))
-- Algebra.Structures.IsCommutativeMonoid._.∙-cong
d_'8729''45'cong_780 ::
  T_IsCommutativeMonoid_736 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_780 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe d_isSemigroup_696 (coe d_isMonoid_746 (coe v0))))
-- Algebra.Structures.IsCommutativeMonoid._.∙-congʳ
d_'8729''45'cong'691'_782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_736 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_782 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_782 v6
du_'8729''45'cong'691'_782 ::
  T_IsCommutativeMonoid_736 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_782 v0
  = let v1 = d_isMonoid_746 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsCommutativeMonoid._.∙-congˡ
d_'8729''45'cong'737'_784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_736 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_784 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_784 v6
du_'8729''45'cong'737'_784 ::
  T_IsCommutativeMonoid_736 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_784 v0
  = let v1 = d_isMonoid_746 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsCommutativeMonoid.isCommutativeSemigroup
d_isCommutativeSemigroup_786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid_736 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeSemigroup_786 v6
du_isCommutativeSemigroup_786 ::
  T_IsCommutativeMonoid_736 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_786 v0
  = coe
      C_IsCommutativeSemigroup'46'constructor_12093
      (coe d_isSemigroup_696 (coe d_isMonoid_746 (coe v0)))
      (coe d_comm_748 (coe v0))
-- Algebra.Structures.IsCommutativeMonoid._.isCommutativeMagma
d_isCommutativeMagma_790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeMonoid_736 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_790 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeMagma_790 v6
du_isCommutativeMagma_790 ::
  T_IsCommutativeMonoid_736 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_790 v0
  = coe
      du_isCommutativeMagma_586
      (coe du_isCommutativeSemigroup_786 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid
d_IsIdempotentMonoid_796 a0 a1 a2 a3 a4 a5 = ()
data T_IsIdempotentMonoid_796
  = C_IsIdempotentMonoid'46'constructor_19237 T_IsMonoid_686
                                              (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsIdempotentMonoid.isMonoid
d_isMonoid_806 :: T_IsIdempotentMonoid_796 -> T_IsMonoid_686
d_isMonoid_806 v0
  = case coe v0 of
      C_IsIdempotentMonoid'46'constructor_19237 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentMonoid.idem
d_idem_808 :: T_IsIdempotentMonoid_796 -> AgdaAny -> AgdaAny
d_idem_808 v0
  = case coe v0 of
      C_IsIdempotentMonoid'46'constructor_19237 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentMonoid._.assoc
d_assoc_812 ::
  T_IsIdempotentMonoid_796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_812 v0
  = coe
      d_assoc_482 (coe d_isSemigroup_696 (coe d_isMonoid_806 (coe v0)))
-- Algebra.Structures.IsIdempotentMonoid._.identity
d_identity_814 ::
  T_IsIdempotentMonoid_796 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_814 v0
  = coe d_identity_698 (coe d_isMonoid_806 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid._.identityʳ
d_identity'691'_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsIdempotentMonoid_796 -> AgdaAny -> AgdaAny
d_identity'691'_816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_816 v6
du_identity'691'_816 ::
  T_IsIdempotentMonoid_796 -> AgdaAny -> AgdaAny
du_identity'691'_816 v0
  = coe du_identity'691'_728 (coe d_isMonoid_806 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid._.identityˡ
d_identity'737'_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsIdempotentMonoid_796 -> AgdaAny -> AgdaAny
d_identity'737'_818 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_818 v6
du_identity'737'_818 ::
  T_IsIdempotentMonoid_796 -> AgdaAny -> AgdaAny
du_identity'737'_818 v0
  = coe du_identity'737'_726 (coe d_isMonoid_806 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid._.isEquivalence
d_isEquivalence_820 ::
  T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_820 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe d_isSemigroup_696 (coe d_isMonoid_806 (coe v0))))
-- Algebra.Structures.IsIdempotentMonoid._.isMagma
d_isMagma_822 :: T_IsIdempotentMonoid_796 -> T_IsMagma_176
d_isMagma_822 v0
  = coe
      d_isMagma_480 (coe d_isSemigroup_696 (coe d_isMonoid_806 (coe v0)))
-- Algebra.Structures.IsIdempotentMonoid._.isPartialEquivalence
d_isPartialEquivalence_824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_824 v6
du_isPartialEquivalence_824 ::
  T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_824 v0
  = let v1 = d_isMonoid_806 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.IsIdempotentMonoid._.isSemigroup
d_isSemigroup_826 :: T_IsIdempotentMonoid_796 -> T_IsSemigroup_472
d_isSemigroup_826 v0
  = coe d_isSemigroup_696 (coe d_isMonoid_806 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid._.isUnitalMagma
d_isUnitalMagma_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsIdempotentMonoid_796 -> T_IsUnitalMagma_642
d_isUnitalMagma_828 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isUnitalMagma_828 v6
du_isUnitalMagma_828 ::
  T_IsIdempotentMonoid_796 -> T_IsUnitalMagma_642
du_isUnitalMagma_828 v0
  = coe du_isUnitalMagma_730 (coe d_isMonoid_806 (coe v0))
-- Algebra.Structures.IsIdempotentMonoid._.refl
d_refl_830 :: T_IsIdempotentMonoid_796 -> AgdaAny -> AgdaAny
d_refl_830 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_isMonoid_806 (coe v0)))))
-- Algebra.Structures.IsIdempotentMonoid._.reflexive
d_reflexive_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentMonoid_796 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_832 v6
du_reflexive_832 ::
  T_IsIdempotentMonoid_796 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_832 v0
  = let v1 = d_isMonoid_806 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_184 (coe v3)) v4)))
-- Algebra.Structures.IsIdempotentMonoid._.setoid
d_setoid_834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_834 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_834 v6
du_setoid_834 ::
  T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_834 v0
  = let v1 = d_isMonoid_806 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsIdempotentMonoid._.sym
d_sym_836 ::
  T_IsIdempotentMonoid_796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_836 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_isMonoid_806 (coe v0)))))
-- Algebra.Structures.IsIdempotentMonoid._.trans
d_trans_838 ::
  T_IsIdempotentMonoid_796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_838 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_isMonoid_806 (coe v0)))))
-- Algebra.Structures.IsIdempotentMonoid._.∙-cong
d_'8729''45'cong_840 ::
  T_IsIdempotentMonoid_796 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_840 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe d_isSemigroup_696 (coe d_isMonoid_806 (coe v0))))
-- Algebra.Structures.IsIdempotentMonoid._.∙-congʳ
d_'8729''45'cong'691'_842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentMonoid_796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_842 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_842 v6
du_'8729''45'cong'691'_842 ::
  T_IsIdempotentMonoid_796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_842 v0
  = let v1 = d_isMonoid_806 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsIdempotentMonoid._.∙-congˡ
d_'8729''45'cong'737'_844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentMonoid_796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_844 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_844 v6
du_'8729''45'cong'737'_844 ::
  T_IsIdempotentMonoid_796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_844 v0
  = let v1 = d_isMonoid_806 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsIdempotentMonoid.isBand
d_isBand_846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsIdempotentMonoid_796 -> T_IsBand_508
d_isBand_846 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isBand_846 v6
du_isBand_846 :: T_IsIdempotentMonoid_796 -> T_IsBand_508
du_isBand_846 v0
  = coe
      C_IsBand'46'constructor_11205
      (coe d_isSemigroup_696 (coe d_isMonoid_806 (coe v0)))
      (coe d_idem_808 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid
d_IsIdempotentCommutativeMonoid_852 a0 a1 a2 a3 a4 a5 = ()
data T_IsIdempotentCommutativeMonoid_852
  = C_IsIdempotentCommutativeMonoid'46'constructor_20685 T_IsCommutativeMonoid_736
                                                         (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsIdempotentCommutativeMonoid.isCommutativeMonoid
d_isCommutativeMonoid_862 ::
  T_IsIdempotentCommutativeMonoid_852 -> T_IsCommutativeMonoid_736
d_isCommutativeMonoid_862 v0
  = case coe v0 of
      C_IsIdempotentCommutativeMonoid'46'constructor_20685 v1 v2
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentCommutativeMonoid.idem
d_idem_864 ::
  T_IsIdempotentCommutativeMonoid_852 -> AgdaAny -> AgdaAny
d_idem_864 v0
  = case coe v0 of
      C_IsIdempotentCommutativeMonoid'46'constructor_20685 v1 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.assoc
d_assoc_868 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_868 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe d_isMonoid_746 (coe d_isCommutativeMonoid_862 (coe v0))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.comm
d_comm_870 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_870 v0
  = coe d_comm_748 (coe d_isCommutativeMonoid_862 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.identity
d_identity_872 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_872 v0
  = coe
      d_identity_698
      (coe d_isMonoid_746 (coe d_isCommutativeMonoid_862 (coe v0)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.identityʳ
d_identity'691'_874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 -> AgdaAny -> AgdaAny
d_identity'691'_874 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_874 v6
du_identity'691'_874 ::
  T_IsIdempotentCommutativeMonoid_852 -> AgdaAny -> AgdaAny
du_identity'691'_874 v0
  = let v1 = d_isCommutativeMonoid_862 (coe v0) in
    coe (coe du_identity'691'_728 (coe d_isMonoid_746 (coe v1)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.identityˡ
d_identity'737'_876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 -> AgdaAny -> AgdaAny
d_identity'737'_876 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_876 v6
du_identity'737'_876 ::
  T_IsIdempotentCommutativeMonoid_852 -> AgdaAny -> AgdaAny
du_identity'737'_876 v0
  = let v1 = d_isCommutativeMonoid_862 (coe v0) in
    coe (coe du_identity'737'_726 (coe d_isMonoid_746 (coe v1)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isCommutativeMagma
d_isCommutativeMagma_878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_878 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeMagma_878 v6
du_isCommutativeMagma_878 ::
  T_IsIdempotentCommutativeMonoid_852 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_878 v0
  = let v1 = d_isCommutativeMonoid_862 (coe v0) in
    coe
      (coe
         du_isCommutativeMagma_586
         (coe du_isCommutativeSemigroup_786 (coe v1)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isCommutativeSemigroup
d_isCommutativeSemigroup_880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_880 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeSemigroup_880 v6
du_isCommutativeSemigroup_880 ::
  T_IsIdempotentCommutativeMonoid_852 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_880 v0
  = coe
      du_isCommutativeSemigroup_786
      (coe d_isCommutativeMonoid_862 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isEquivalence
d_isEquivalence_882 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_882 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe d_isMonoid_746 (coe d_isCommutativeMonoid_862 (coe v0)))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isMagma
d_isMagma_884 ::
  T_IsIdempotentCommutativeMonoid_852 -> T_IsMagma_176
d_isMagma_884 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe d_isMonoid_746 (coe d_isCommutativeMonoid_862 (coe v0))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isMonoid
d_isMonoid_886 ::
  T_IsIdempotentCommutativeMonoid_852 -> T_IsMonoid_686
d_isMonoid_886 v0
  = coe d_isMonoid_746 (coe d_isCommutativeMonoid_862 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isPartialEquivalence
d_isPartialEquivalence_888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_888 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_888 v6
du_isPartialEquivalence_888 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_888 v0
  = let v1 = d_isCommutativeMonoid_862 (coe v0) in
    coe
      (let v2 = d_isMonoid_746 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe
            (let v4 = d_isMagma_480 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe d_isEquivalence_184 (coe v4))))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isSemigroup
d_isSemigroup_890 ::
  T_IsIdempotentCommutativeMonoid_852 -> T_IsSemigroup_472
d_isSemigroup_890 v0
  = coe
      d_isSemigroup_696
      (coe d_isMonoid_746 (coe d_isCommutativeMonoid_862 (coe v0)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isUnitalMagma
d_isUnitalMagma_892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 -> T_IsUnitalMagma_642
d_isUnitalMagma_892 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isUnitalMagma_892 v6
du_isUnitalMagma_892 ::
  T_IsIdempotentCommutativeMonoid_852 -> T_IsUnitalMagma_642
du_isUnitalMagma_892 v0
  = let v1 = d_isCommutativeMonoid_862 (coe v0) in
    coe (coe du_isUnitalMagma_730 (coe d_isMonoid_746 (coe v1)))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.refl
d_refl_894 ::
  T_IsIdempotentCommutativeMonoid_852 -> AgdaAny -> AgdaAny
d_refl_894 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe d_isMonoid_746 (coe d_isCommutativeMonoid_862 (coe v0))))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.reflexive
d_reflexive_896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_896 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_896 v6
du_reflexive_896 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_896 v0
  = let v1 = d_isCommutativeMonoid_862 (coe v0) in
    coe
      (let v2 = d_isMonoid_746 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe
            (let v4 = d_isMagma_480 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe d_isEquivalence_184 (coe v4)) v5))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.setoid
d_setoid_898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_898 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_898 v6
du_setoid_898 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_898 v0
  = let v1 = d_isCommutativeMonoid_862 (coe v0) in
    coe
      (let v2 = d_isMonoid_746 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.sym
d_sym_900 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_900 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe d_isMonoid_746 (coe d_isCommutativeMonoid_862 (coe v0))))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.trans
d_trans_902 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_902 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe d_isMonoid_746 (coe d_isCommutativeMonoid_862 (coe v0))))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.∙-cong
d_'8729''45'cong_904 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_904 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe d_isMonoid_746 (coe d_isCommutativeMonoid_862 (coe v0)))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.∙-congʳ
d_'8729''45'cong'691'_906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_906 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_906 v6
du_'8729''45'cong'691'_906 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_906 v0
  = let v1 = d_isCommutativeMonoid_862 (coe v0) in
    coe
      (let v2 = d_isMonoid_746 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.∙-congˡ
d_'8729''45'cong'737'_908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_908 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_908 v6
du_'8729''45'cong'737'_908 ::
  T_IsIdempotentCommutativeMonoid_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_908 v0
  = let v1 = d_isCommutativeMonoid_862 (coe v0) in
    coe
      (let v2 = d_isMonoid_746 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsIdempotentCommutativeMonoid.isIdempotentMonoid
d_isIdempotentMonoid_910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 -> T_IsIdempotentMonoid_796
d_isIdempotentMonoid_910 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isIdempotentMonoid_910 v6
du_isIdempotentMonoid_910 ::
  T_IsIdempotentCommutativeMonoid_852 -> T_IsIdempotentMonoid_796
du_isIdempotentMonoid_910 v0
  = coe
      C_IsIdempotentMonoid'46'constructor_19237
      (coe d_isMonoid_746 (coe d_isCommutativeMonoid_862 (coe v0)))
      (coe d_idem_864 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid._.isBand
d_isBand_914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsIdempotentCommutativeMonoid_852 -> T_IsBand_508
d_isBand_914 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isBand_914 v6
du_isBand_914 ::
  T_IsIdempotentCommutativeMonoid_852 -> T_IsBand_508
du_isBand_914 v0
  = coe du_isBand_846 (coe du_isIdempotentMonoid_910 (coe v0))
-- Algebra.Structures.IsIdempotentCommutativeMonoid.isCommutativeBand
d_isCommutativeBand_916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsIdempotentCommutativeMonoid_852 -> T_IsCommutativeBand_590
d_isCommutativeBand_916 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeBand_916 v6
du_isCommutativeBand_916 ::
  T_IsIdempotentCommutativeMonoid_852 -> T_IsCommutativeBand_590
du_isCommutativeBand_916 v0
  = coe
      C_IsCommutativeBand'46'constructor_13109
      (coe du_isBand_846 (coe du_isIdempotentMonoid_910 (coe v0)))
      (coe d_comm_748 (coe d_isCommutativeMonoid_862 (coe v0)))
-- Algebra.Structures.IsInvertibleMagma
d_IsInvertibleMagma_924 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsInvertibleMagma_924
  = C_IsInvertibleMagma'46'constructor_22695 T_IsMagma_176
                                             MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                             (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsInvertibleMagma.isMagma
d_isMagma_938 :: T_IsInvertibleMagma_924 -> T_IsMagma_176
d_isMagma_938 v0
  = case coe v0 of
      C_IsInvertibleMagma'46'constructor_22695 v1 v2 v3 -> coe v1
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsInvertibleMagma.inverse
d_inverse_940 ::
  T_IsInvertibleMagma_924 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_940 v0
  = case coe v0 of
      C_IsInvertibleMagma'46'constructor_22695 v1 v2 v3 -> coe v2
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsInvertibleMagma.⁻¹-cong
d_'8315''185''45'cong_942 ::
  T_IsInvertibleMagma_924 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_942 v0
  = case coe v0 of
      C_IsInvertibleMagma'46'constructor_22695 v1 v2 v3 -> coe v3
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsInvertibleMagma._.isEquivalence
d_isEquivalence_946 ::
  T_IsInvertibleMagma_924 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_946 v0
  = coe d_isEquivalence_184 (coe d_isMagma_938 (coe v0))
-- Algebra.Structures.IsInvertibleMagma._.isPartialEquivalence
d_isPartialEquivalence_948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_924 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_948 v7
du_isPartialEquivalence_948 ::
  T_IsInvertibleMagma_924 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_948 v0
  = let v1 = d_isMagma_938 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_184 (coe v1)))
-- Algebra.Structures.IsInvertibleMagma._.refl
d_refl_950 :: T_IsInvertibleMagma_924 -> AgdaAny -> AgdaAny
d_refl_950 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe d_isMagma_938 (coe v0)))
-- Algebra.Structures.IsInvertibleMagma._.reflexive
d_reflexive_952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_924 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_952 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_952 v7
du_reflexive_952 ::
  T_IsInvertibleMagma_924 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_952 v0
  = let v1 = d_isMagma_938 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_184 (coe v1)) v2)
-- Algebra.Structures.IsInvertibleMagma._.setoid
d_setoid_954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_924 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_954 v7
du_setoid_954 ::
  T_IsInvertibleMagma_924 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_954 v0 = coe du_setoid_200 (coe d_isMagma_938 (coe v0))
-- Algebra.Structures.IsInvertibleMagma._.sym
d_sym_956 ::
  T_IsInvertibleMagma_924 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_956 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe d_isMagma_938 (coe v0)))
-- Algebra.Structures.IsInvertibleMagma._.trans
d_trans_958 ::
  T_IsInvertibleMagma_924 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_958 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe d_isMagma_938 (coe v0)))
-- Algebra.Structures.IsInvertibleMagma._.∙-cong
d_'8729''45'cong_960 ::
  T_IsInvertibleMagma_924 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_960 v0
  = coe d_'8729''45'cong_186 (coe d_isMagma_938 (coe v0))
-- Algebra.Structures.IsInvertibleMagma._.∙-congʳ
d_'8729''45'cong'691'_962 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_924 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_962 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_962 v7
du_'8729''45'cong'691'_962 ::
  T_IsInvertibleMagma_924 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_962 v0
  = coe du_'8729''45'cong'691'_206 (coe d_isMagma_938 (coe v0))
-- Algebra.Structures.IsInvertibleMagma._.∙-congˡ
d_'8729''45'cong'737'_964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_924 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_964 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_964 v7
du_'8729''45'cong'737'_964 ::
  T_IsInvertibleMagma_924 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_964 v0
  = coe du_'8729''45'cong'737'_202 (coe d_isMagma_938 (coe v0))
-- Algebra.Structures.IsInvertibleMagma.inverseˡ
d_inverse'737'_966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_924 -> AgdaAny -> AgdaAny
d_inverse'737'_966 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'737'_966 v7
du_inverse'737'_966 ::
  T_IsInvertibleMagma_924 -> AgdaAny -> AgdaAny
du_inverse'737'_966 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_inverse_940 (coe v0))
-- Algebra.Structures.IsInvertibleMagma.inverseʳ
d_inverse'691'_968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleMagma_924 -> AgdaAny -> AgdaAny
d_inverse'691'_968 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'691'_968 v7
du_inverse'691'_968 ::
  T_IsInvertibleMagma_924 -> AgdaAny -> AgdaAny
du_inverse'691'_968 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_inverse_940 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma
d_IsInvertibleUnitalMagma_976 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsInvertibleUnitalMagma_976
  = C_IsInvertibleUnitalMagma'46'constructor_24571 T_IsInvertibleMagma_924
                                                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsInvertibleUnitalMagma.isInvertibleMagma
d_isInvertibleMagma_988 ::
  T_IsInvertibleUnitalMagma_976 -> T_IsInvertibleMagma_924
d_isInvertibleMagma_988 v0
  = case coe v0 of
      C_IsInvertibleUnitalMagma'46'constructor_24571 v1 v2 -> coe v1
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsInvertibleUnitalMagma.identity
d_identity_990 ::
  T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_990 v0
  = case coe v0 of
      C_IsInvertibleUnitalMagma'46'constructor_24571 v1 v2 -> coe v2
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsInvertibleUnitalMagma._.inverse
d_inverse_994 ::
  T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_994 v0
  = coe d_inverse_940 (coe d_isInvertibleMagma_988 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma._.inverseʳ
d_inverse'691'_996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_976 -> AgdaAny -> AgdaAny
d_inverse'691'_996 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'691'_996 v7
du_inverse'691'_996 ::
  T_IsInvertibleUnitalMagma_976 -> AgdaAny -> AgdaAny
du_inverse'691'_996 v0
  = coe du_inverse'691'_968 (coe d_isInvertibleMagma_988 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma._.inverseˡ
d_inverse'737'_998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_976 -> AgdaAny -> AgdaAny
d_inverse'737'_998 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'737'_998 v7
du_inverse'737'_998 ::
  T_IsInvertibleUnitalMagma_976 -> AgdaAny -> AgdaAny
du_inverse'737'_998 v0
  = coe du_inverse'737'_966 (coe d_isInvertibleMagma_988 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma._.isEquivalence
d_isEquivalence_1000 ::
  T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1000 v0
  = coe
      d_isEquivalence_184
      (coe d_isMagma_938 (coe d_isInvertibleMagma_988 (coe v0)))
-- Algebra.Structures.IsInvertibleUnitalMagma._.isMagma
d_isMagma_1002 :: T_IsInvertibleUnitalMagma_976 -> T_IsMagma_176
d_isMagma_1002 v0
  = coe d_isMagma_938 (coe d_isInvertibleMagma_988 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma._.isPartialEquivalence
d_isPartialEquivalence_1004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1004 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1004 v7
du_isPartialEquivalence_1004 ::
  T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1004 v0
  = let v1 = d_isInvertibleMagma_988 (coe v0) in
    coe
      (let v2 = d_isMagma_938 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe d_isEquivalence_184 (coe v2))))
-- Algebra.Structures.IsInvertibleUnitalMagma._.refl
d_refl_1006 :: T_IsInvertibleUnitalMagma_976 -> AgdaAny -> AgdaAny
d_refl_1006 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe d_isMagma_938 (coe d_isInvertibleMagma_988 (coe v0))))
-- Algebra.Structures.IsInvertibleUnitalMagma._.reflexive
d_reflexive_1008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_976 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1008 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1008 v7
du_reflexive_1008 ::
  T_IsInvertibleUnitalMagma_976 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1008 v0
  = let v1 = d_isInvertibleMagma_988 (coe v0) in
    coe
      (let v2 = d_isMagma_938 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe d_isEquivalence_184 (coe v2)) v3))
-- Algebra.Structures.IsInvertibleUnitalMagma._.setoid
d_setoid_1010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1010 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1010 v7
du_setoid_1010 ::
  T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1010 v0
  = let v1 = d_isInvertibleMagma_988 (coe v0) in
    coe (coe du_setoid_200 (coe d_isMagma_938 (coe v1)))
-- Algebra.Structures.IsInvertibleUnitalMagma._.sym
d_sym_1012 ::
  T_IsInvertibleUnitalMagma_976 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1012 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe d_isMagma_938 (coe d_isInvertibleMagma_988 (coe v0))))
-- Algebra.Structures.IsInvertibleUnitalMagma._.trans
d_trans_1014 ::
  T_IsInvertibleUnitalMagma_976 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1014 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe d_isMagma_938 (coe d_isInvertibleMagma_988 (coe v0))))
-- Algebra.Structures.IsInvertibleUnitalMagma._.⁻¹-cong
d_'8315''185''45'cong_1016 ::
  T_IsInvertibleUnitalMagma_976 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_1016 v0
  = coe
      d_'8315''185''45'cong_942 (coe d_isInvertibleMagma_988 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma._.∙-cong
d_'8729''45'cong_1018 ::
  T_IsInvertibleUnitalMagma_976 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1018 v0
  = coe
      d_'8729''45'cong_186
      (coe d_isMagma_938 (coe d_isInvertibleMagma_988 (coe v0)))
-- Algebra.Structures.IsInvertibleUnitalMagma._.∙-congʳ
d_'8729''45'cong'691'_1020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_976 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1020 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1020 v7
du_'8729''45'cong'691'_1020 ::
  T_IsInvertibleUnitalMagma_976 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1020 v0
  = let v1 = d_isInvertibleMagma_988 (coe v0) in
    coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_938 (coe v1)))
-- Algebra.Structures.IsInvertibleUnitalMagma._.∙-congˡ
d_'8729''45'cong'737'_1022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_976 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1022 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1022 v7
du_'8729''45'cong'737'_1022 ::
  T_IsInvertibleUnitalMagma_976 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1022 v0
  = let v1 = d_isInvertibleMagma_988 (coe v0) in
    coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_938 (coe v1)))
-- Algebra.Structures.IsInvertibleUnitalMagma.identityˡ
d_identity'737'_1024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_976 -> AgdaAny -> AgdaAny
d_identity'737'_1024 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_1024 v7
du_identity'737'_1024 ::
  T_IsInvertibleUnitalMagma_976 -> AgdaAny -> AgdaAny
du_identity'737'_1024 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_identity_990 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma.identityʳ
d_identity'691'_1026 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_976 -> AgdaAny -> AgdaAny
d_identity'691'_1026 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_1026 v7
du_identity'691'_1026 ::
  T_IsInvertibleUnitalMagma_976 -> AgdaAny -> AgdaAny
du_identity'691'_1026 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_identity_990 (coe v0))
-- Algebra.Structures.IsInvertibleUnitalMagma.isUnitalMagma
d_isUnitalMagma_1028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsInvertibleUnitalMagma_976 -> T_IsUnitalMagma_642
d_isUnitalMagma_1028 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isUnitalMagma_1028 v7
du_isUnitalMagma_1028 ::
  T_IsInvertibleUnitalMagma_976 -> T_IsUnitalMagma_642
du_isUnitalMagma_1028 v0
  = coe
      C_IsUnitalMagma'46'constructor_14317
      (coe d_isMagma_938 (coe d_isInvertibleMagma_988 (coe v0)))
      (coe d_identity_990 (coe v0))
-- Algebra.Structures.IsGroup
d_IsGroup_1036 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsGroup_1036
  = C_IsGroup'46'constructor_26963 T_IsMonoid_686
                                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                   (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsGroup.isMonoid
d_isMonoid_1050 :: T_IsGroup_1036 -> T_IsMonoid_686
d_isMonoid_1050 v0
  = case coe v0 of
      C_IsGroup'46'constructor_26963 v1 v2 v3 -> coe v1
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsGroup.inverse
d_inverse_1052 ::
  T_IsGroup_1036 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1052 v0
  = case coe v0 of
      C_IsGroup'46'constructor_26963 v1 v2 v3 -> coe v2
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsGroup.⁻¹-cong
d_'8315''185''45'cong_1054 ::
  T_IsGroup_1036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_1054 v0
  = case coe v0 of
      C_IsGroup'46'constructor_26963 v1 v2 v3 -> coe v3
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsGroup._.assoc
d_assoc_1058 ::
  T_IsGroup_1036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1058 v0
  = coe
      d_assoc_482 (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v0)))
-- Algebra.Structures.IsGroup._.identity
d_identity_1060 ::
  T_IsGroup_1036 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1060 v0
  = coe d_identity_698 (coe d_isMonoid_1050 (coe v0))
-- Algebra.Structures.IsGroup._.identityʳ
d_identity'691'_1062 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1036 -> AgdaAny -> AgdaAny
d_identity'691'_1062 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_1062 v7
du_identity'691'_1062 :: T_IsGroup_1036 -> AgdaAny -> AgdaAny
du_identity'691'_1062 v0
  = coe du_identity'691'_728 (coe d_isMonoid_1050 (coe v0))
-- Algebra.Structures.IsGroup._.identityˡ
d_identity'737'_1064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1036 -> AgdaAny -> AgdaAny
d_identity'737'_1064 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_1064 v7
du_identity'737'_1064 :: T_IsGroup_1036 -> AgdaAny -> AgdaAny
du_identity'737'_1064 v0
  = coe du_identity'737'_726 (coe d_isMonoid_1050 (coe v0))
-- Algebra.Structures.IsGroup._.isEquivalence
d_isEquivalence_1066 ::
  T_IsGroup_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1066 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v0))))
-- Algebra.Structures.IsGroup._.isMagma
d_isMagma_1068 :: T_IsGroup_1036 -> T_IsMagma_176
d_isMagma_1068 v0
  = coe
      d_isMagma_480
      (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v0)))
-- Algebra.Structures.IsGroup._.isPartialEquivalence
d_isPartialEquivalence_1070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1070 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1070 v7
du_isPartialEquivalence_1070 ::
  T_IsGroup_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1070 v0
  = let v1 = d_isMonoid_1050 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.IsGroup._.isSemigroup
d_isSemigroup_1072 :: T_IsGroup_1036 -> T_IsSemigroup_472
d_isSemigroup_1072 v0
  = coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v0))
-- Algebra.Structures.IsGroup._.isUnitalMagma
d_isUnitalMagma_1074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1036 -> T_IsUnitalMagma_642
d_isUnitalMagma_1074 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isUnitalMagma_1074 v7
du_isUnitalMagma_1074 :: T_IsGroup_1036 -> T_IsUnitalMagma_642
du_isUnitalMagma_1074 v0
  = coe du_isUnitalMagma_730 (coe d_isMonoid_1050 (coe v0))
-- Algebra.Structures.IsGroup._.refl
d_refl_1076 :: T_IsGroup_1036 -> AgdaAny -> AgdaAny
d_refl_1076 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v0)))))
-- Algebra.Structures.IsGroup._.reflexive
d_reflexive_1078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1078 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1078 v7
du_reflexive_1078 ::
  T_IsGroup_1036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1078 v0
  = let v1 = d_isMonoid_1050 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_184 (coe v3)) v4)))
-- Algebra.Structures.IsGroup._.setoid
d_setoid_1080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1080 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1080 v7
du_setoid_1080 ::
  T_IsGroup_1036 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1080 v0
  = let v1 = d_isMonoid_1050 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsGroup._.sym
d_sym_1082 ::
  T_IsGroup_1036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1082 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v0)))))
-- Algebra.Structures.IsGroup._.trans
d_trans_1084 ::
  T_IsGroup_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1084 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v0)))))
-- Algebra.Structures.IsGroup._.∙-cong
d_'8729''45'cong_1086 ::
  T_IsGroup_1036 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1086 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v0))))
-- Algebra.Structures.IsGroup._.∙-congʳ
d_'8729''45'cong'691'_1088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1088 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1088 v7
du_'8729''45'cong'691'_1088 ::
  T_IsGroup_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1088 v0
  = let v1 = d_isMonoid_1050 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsGroup._.∙-congˡ
d_'8729''45'cong'737'_1090 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1090 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1090 v7
du_'8729''45'cong'737'_1090 ::
  T_IsGroup_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1090 v0
  = let v1 = d_isMonoid_1050 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsGroup._\\_
d__'92''92'__1092 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 -> AgdaAny -> AgdaAny -> AgdaAny
d__'92''92'__1092 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 v8 v9
  = du__'92''92'__1092 v4 v6 v8 v9
du__'92''92'__1092 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'92''92'__1092 v0 v1 v2 v3 = coe v0 (coe v1 v2) v3
-- Algebra.Structures.IsGroup._//_
d__'47''47'__1098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__1098 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 v8 v9
  = du__'47''47'__1098 v4 v6 v8 v9
du__'47''47'__1098 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__1098 v0 v1 v2 v3 = coe v0 v2 (coe v1 v3)
-- Algebra.Structures.IsGroup._-_
d__'45'__1104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 -> AgdaAny -> AgdaAny -> AgdaAny
d__'45'__1104 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 = du__'45'__1104 v4 v6
du__'45'__1104 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'45'__1104 v0 v1 = coe du__'47''47'__1098 (coe v0) (coe v1)
-- Algebra.Structures.IsGroup.inverseˡ
d_inverse'737'_1106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1036 -> AgdaAny -> AgdaAny
d_inverse'737'_1106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'737'_1106 v7
du_inverse'737'_1106 :: T_IsGroup_1036 -> AgdaAny -> AgdaAny
du_inverse'737'_1106 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_inverse_1052 (coe v0))
-- Algebra.Structures.IsGroup.inverseʳ
d_inverse'691'_1108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1036 -> AgdaAny -> AgdaAny
d_inverse'691'_1108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'691'_1108 v7
du_inverse'691'_1108 :: T_IsGroup_1036 -> AgdaAny -> AgdaAny
du_inverse'691'_1108 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_inverse_1052 (coe v0))
-- Algebra.Structures.IsGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_1114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_1114 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'737''45''8315''185'_1114 v4 v5 v6 v7
du_unique'737''45''8315''185'_1114 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_1114 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'id'8743'inv'691''8658'inv'737''45'unique_456
      (let v4 = d_isSemigroup_696 (coe d_isMonoid_1050 (coe v3)) in
       coe (coe du_setoid_200 (coe d_isMagma_480 (coe v4))))
      (coe v0) (coe v2) (coe v1)
      (coe
         d_'8729''45'cong_186
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v3)))))
      (coe
         d_assoc_482 (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v3))))
      (coe d_identity_698 (coe d_isMonoid_1050 (coe v3)))
      (coe du_inverse'691'_1108 (coe v3))
-- Algebra.Structures.IsGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_1120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_1120 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'691''45''8315''185'_1120 v4 v5 v6 v7
du_unique'691''45''8315''185'_1120 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_1120 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'id'8743'inv'737''8658'inv'691''45'unique_476
      (let v4 = d_isSemigroup_696 (coe d_isMonoid_1050 (coe v3)) in
       coe (coe du_setoid_200 (coe d_isMagma_480 (coe v4))))
      (coe v0) (coe v2) (coe v1)
      (coe
         d_'8729''45'cong_186
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v3)))))
      (coe
         d_assoc_482 (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v3))))
      (coe d_identity_698 (coe d_isMonoid_1050 (coe v3)))
      (coe du_inverse'737'_1106 (coe v3))
-- Algebra.Structures.IsGroup.isInvertibleMagma
d_isInvertibleMagma_1122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsGroup_1036 -> T_IsInvertibleMagma_924
d_isInvertibleMagma_1122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleMagma_1122 v7
du_isInvertibleMagma_1122 ::
  T_IsGroup_1036 -> T_IsInvertibleMagma_924
du_isInvertibleMagma_1122 v0
  = coe
      C_IsInvertibleMagma'46'constructor_22695
      (coe
         d_isMagma_480
         (coe d_isSemigroup_696 (coe d_isMonoid_1050 (coe v0))))
      (coe d_inverse_1052 (coe v0))
      (coe d_'8315''185''45'cong_1054 (coe v0))
-- Algebra.Structures.IsGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_1124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsGroup_1036 -> T_IsInvertibleUnitalMagma_976
d_isInvertibleUnitalMagma_1124 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleUnitalMagma_1124 v7
du_isInvertibleUnitalMagma_1124 ::
  T_IsGroup_1036 -> T_IsInvertibleUnitalMagma_976
du_isInvertibleUnitalMagma_1124 v0
  = coe
      C_IsInvertibleUnitalMagma'46'constructor_24571
      (coe du_isInvertibleMagma_1122 (coe v0))
      (coe d_identity_698 (coe d_isMonoid_1050 (coe v0)))
-- Algebra.Structures.IsAbelianGroup
d_IsAbelianGroup_1132 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsAbelianGroup_1132
  = C_IsAbelianGroup'46'constructor_32441 T_IsGroup_1036
                                          (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsAbelianGroup.isGroup
d_isGroup_1144 :: T_IsAbelianGroup_1132 -> T_IsGroup_1036
d_isGroup_1144 v0
  = case coe v0 of
      C_IsAbelianGroup'46'constructor_32441 v1 v2 -> coe v1
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsAbelianGroup.comm
d_comm_1146 ::
  T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_1146 v0
  = case coe v0 of
      C_IsAbelianGroup'46'constructor_32441 v1 v2 -> coe v2
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsAbelianGroup._._//_
d__'47''47'__1150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__1150 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7
  = du__'47''47'__1150 v4 v6
du__'47''47'__1150 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__1150 v0 v1 = coe du__'47''47'__1098 (coe v0) (coe v1)
-- Algebra.Structures.IsAbelianGroup._.assoc
d_assoc_1152 ::
  T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1152 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe d_isMonoid_1050 (coe d_isGroup_1144 (coe v0))))
-- Algebra.Structures.IsAbelianGroup._.identity
d_identity_1154 ::
  T_IsAbelianGroup_1132 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1154 v0
  = coe
      d_identity_698 (coe d_isMonoid_1050 (coe d_isGroup_1144 (coe v0)))
-- Algebra.Structures.IsAbelianGroup._.identityʳ
d_identity'691'_1156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny
d_identity'691'_1156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_1156 v7
du_identity'691'_1156 ::
  T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny
du_identity'691'_1156 v0
  = let v1 = d_isGroup_1144 (coe v0) in
    coe (coe du_identity'691'_728 (coe d_isMonoid_1050 (coe v1)))
-- Algebra.Structures.IsAbelianGroup._.identityˡ
d_identity'737'_1158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny
d_identity'737'_1158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_1158 v7
du_identity'737'_1158 ::
  T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny
du_identity'737'_1158 v0
  = let v1 = d_isGroup_1144 (coe v0) in
    coe (coe du_identity'737'_726 (coe d_isMonoid_1050 (coe v1)))
-- Algebra.Structures.IsAbelianGroup._.inverse
d_inverse_1160 ::
  T_IsAbelianGroup_1132 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1160 v0
  = coe d_inverse_1052 (coe d_isGroup_1144 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.inverseʳ
d_inverse'691'_1162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny
d_inverse'691'_1162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'691'_1162 v7
du_inverse'691'_1162 :: T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny
du_inverse'691'_1162 v0
  = coe du_inverse'691'_1108 (coe d_isGroup_1144 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.inverseˡ
d_inverse'737'_1164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny
d_inverse'737'_1164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'737'_1164 v7
du_inverse'737'_1164 :: T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny
du_inverse'737'_1164 v0
  = coe du_inverse'737'_1106 (coe d_isGroup_1144 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.isEquivalence
d_isEquivalence_1166 ::
  T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1166 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe d_isMonoid_1050 (coe d_isGroup_1144 (coe v0)))))
-- Algebra.Structures.IsAbelianGroup._.isInvertibleMagma
d_isInvertibleMagma_1168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 -> T_IsInvertibleMagma_924
d_isInvertibleMagma_1168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleMagma_1168 v7
du_isInvertibleMagma_1168 ::
  T_IsAbelianGroup_1132 -> T_IsInvertibleMagma_924
du_isInvertibleMagma_1168 v0
  = coe du_isInvertibleMagma_1122 (coe d_isGroup_1144 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_1170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 -> T_IsInvertibleUnitalMagma_976
d_isInvertibleUnitalMagma_1170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleUnitalMagma_1170 v7
du_isInvertibleUnitalMagma_1170 ::
  T_IsAbelianGroup_1132 -> T_IsInvertibleUnitalMagma_976
du_isInvertibleUnitalMagma_1170 v0
  = coe du_isInvertibleUnitalMagma_1124 (coe d_isGroup_1144 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.isMagma
d_isMagma_1172 :: T_IsAbelianGroup_1132 -> T_IsMagma_176
d_isMagma_1172 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe d_isMonoid_1050 (coe d_isGroup_1144 (coe v0))))
-- Algebra.Structures.IsAbelianGroup._.isMonoid
d_isMonoid_1174 :: T_IsAbelianGroup_1132 -> T_IsMonoid_686
d_isMonoid_1174 v0
  = coe d_isMonoid_1050 (coe d_isGroup_1144 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.isPartialEquivalence
d_isPartialEquivalence_1176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1176 v7
du_isPartialEquivalence_1176 ::
  T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1176 v0
  = let v1 = d_isGroup_1144 (coe v0) in
    coe
      (let v2 = d_isMonoid_1050 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe
            (let v4 = d_isMagma_480 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe d_isEquivalence_184 (coe v4))))))
-- Algebra.Structures.IsAbelianGroup._.isSemigroup
d_isSemigroup_1178 :: T_IsAbelianGroup_1132 -> T_IsSemigroup_472
d_isSemigroup_1178 v0
  = coe
      d_isSemigroup_696
      (coe d_isMonoid_1050 (coe d_isGroup_1144 (coe v0)))
-- Algebra.Structures.IsAbelianGroup._.isUnitalMagma
d_isUnitalMagma_1180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 -> T_IsUnitalMagma_642
d_isUnitalMagma_1180 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isUnitalMagma_1180 v7
du_isUnitalMagma_1180 ::
  T_IsAbelianGroup_1132 -> T_IsUnitalMagma_642
du_isUnitalMagma_1180 v0
  = let v1 = d_isGroup_1144 (coe v0) in
    coe (coe du_isUnitalMagma_730 (coe d_isMonoid_1050 (coe v1)))
-- Algebra.Structures.IsAbelianGroup._.refl
d_refl_1182 :: T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny
d_refl_1182 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe d_isMonoid_1050 (coe d_isGroup_1144 (coe v0))))))
-- Algebra.Structures.IsAbelianGroup._.reflexive
d_reflexive_1184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1184 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1184 v7
du_reflexive_1184 ::
  T_IsAbelianGroup_1132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1184 v0
  = let v1 = d_isGroup_1144 (coe v0) in
    coe
      (let v2 = d_isMonoid_1050 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe
            (let v4 = d_isMagma_480 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe d_isEquivalence_184 (coe v4)) v5))))
-- Algebra.Structures.IsAbelianGroup._.setoid
d_setoid_1186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1186 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1186 v7
du_setoid_1186 ::
  T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1186 v0
  = let v1 = d_isGroup_1144 (coe v0) in
    coe
      (let v2 = d_isMonoid_1050 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsAbelianGroup._.sym
d_sym_1188 ::
  T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1188 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe d_isMonoid_1050 (coe d_isGroup_1144 (coe v0))))))
-- Algebra.Structures.IsAbelianGroup._.trans
d_trans_1190 ::
  T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1190 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe d_isMonoid_1050 (coe d_isGroup_1144 (coe v0))))))
-- Algebra.Structures.IsAbelianGroup._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_1192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_1192 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'691''45''8315''185'_1192 v4 v5 v6 v7
du_unique'691''45''8315''185'_1192 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_1192 v0 v1 v2 v3
  = coe
      du_unique'691''45''8315''185'_1120 (coe v0) (coe v1) (coe v2)
      (coe d_isGroup_1144 (coe v3))
-- Algebra.Structures.IsAbelianGroup._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_1194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_1194 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'737''45''8315''185'_1194 v4 v5 v6 v7
du_unique'737''45''8315''185'_1194 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_1194 v0 v1 v2 v3
  = coe
      du_unique'737''45''8315''185'_1114 (coe v0) (coe v1) (coe v2)
      (coe d_isGroup_1144 (coe v3))
-- Algebra.Structures.IsAbelianGroup._.⁻¹-cong
d_'8315''185''45'cong_1196 ::
  T_IsAbelianGroup_1132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_1196 v0
  = coe d_'8315''185''45'cong_1054 (coe d_isGroup_1144 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.∙-cong
d_'8729''45'cong_1198 ::
  T_IsAbelianGroup_1132 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1198 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe d_isMonoid_1050 (coe d_isGroup_1144 (coe v0)))))
-- Algebra.Structures.IsAbelianGroup._.∙-congʳ
d_'8729''45'cong'691'_1200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1200 v7
du_'8729''45'cong'691'_1200 ::
  T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1200 v0
  = let v1 = d_isGroup_1144 (coe v0) in
    coe
      (let v2 = d_isMonoid_1050 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsAbelianGroup._.∙-congˡ
d_'8729''45'cong'737'_1202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1202 v7
du_'8729''45'cong'737'_1202 ::
  T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1202 v0
  = let v1 = d_isGroup_1144 (coe v0) in
    coe
      (let v2 = d_isMonoid_1050 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsAbelianGroup.isCommutativeMonoid
d_isCommutativeMonoid_1204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 -> T_IsCommutativeMonoid_736
d_isCommutativeMonoid_1204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMonoid_1204 v7
du_isCommutativeMonoid_1204 ::
  T_IsAbelianGroup_1132 -> T_IsCommutativeMonoid_736
du_isCommutativeMonoid_1204 v0
  = coe
      C_IsCommutativeMonoid'46'constructor_17695
      (coe d_isMonoid_1050 (coe d_isGroup_1144 (coe v0)))
      (coe d_comm_1146 (coe v0))
-- Algebra.Structures.IsAbelianGroup._.isCommutativeMagma
d_isCommutativeMagma_1208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_1208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMagma_1208 v7
du_isCommutativeMagma_1208 ::
  T_IsAbelianGroup_1132 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_1208 v0
  = let v1 = coe du_isCommutativeMonoid_1204 (coe v0) in
    coe
      (coe
         du_isCommutativeMagma_586
         (coe du_isCommutativeSemigroup_786 (coe v1)))
-- Algebra.Structures.IsAbelianGroup._.isCommutativeSemigroup
d_isCommutativeSemigroup_1210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroup_1132 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_1210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeSemigroup_1210 v7
du_isCommutativeSemigroup_1210 ::
  T_IsAbelianGroup_1132 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_1210 v0
  = coe
      du_isCommutativeSemigroup_786
      (coe du_isCommutativeMonoid_1204 (coe v0))
-- Algebra.Structures.IsNearSemiring
d_IsNearSemiring_1218 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsNearSemiring_1218
  = C_IsNearSemiring'46'constructor_35025 T_IsMonoid_686
                                          (AgdaAny ->
                                           AgdaAny ->
                                           AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsNearSemiring.+-isMonoid
d_'43''45'isMonoid_1236 :: T_IsNearSemiring_1218 -> T_IsMonoid_686
d_'43''45'isMonoid_1236 v0
  = case coe v0 of
      C_IsNearSemiring'46'constructor_35025 v1 v2 v3 v4 v5 -> coe v1
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearSemiring.*-cong
d_'42''45'cong_1238 ::
  T_IsNearSemiring_1218 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1238 v0
  = case coe v0 of
      C_IsNearSemiring'46'constructor_35025 v1 v2 v3 v4 v5 -> coe v2
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearSemiring.*-assoc
d_'42''45'assoc_1240 ::
  T_IsNearSemiring_1218 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1240 v0
  = case coe v0 of
      C_IsNearSemiring'46'constructor_35025 v1 v2 v3 v4 v5 -> coe v3
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearSemiring.distribʳ
d_distrib'691'_1242 ::
  T_IsNearSemiring_1218 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1242 v0
  = case coe v0 of
      C_IsNearSemiring'46'constructor_35025 v1 v2 v3 v4 v5 -> coe v4
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearSemiring.zeroˡ
d_zero'737'_1244 :: T_IsNearSemiring_1218 -> AgdaAny -> AgdaAny
d_zero'737'_1244 v0
  = case coe v0 of
      C_IsNearSemiring'46'constructor_35025 v1 v2 v3 v4 v5 -> coe v5
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearSemiring._.assoc
d_assoc_1248 ::
  T_IsNearSemiring_1218 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1248 v0
  = coe
      d_assoc_482
      (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_1236 (coe v0)))
-- Algebra.Structures.IsNearSemiring._.∙-cong
d_'8729''45'cong_1250 ::
  T_IsNearSemiring_1218 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1250 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_1236 (coe v0))))
-- Algebra.Structures.IsNearSemiring._.∙-congʳ
d_'8729''45'cong'691'_1252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1252 v7
du_'8729''45'cong'691'_1252 ::
  T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1252 v0
  = let v1 = d_'43''45'isMonoid_1236 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsNearSemiring._.∙-congˡ
d_'8729''45'cong'737'_1254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1254 v7
du_'8729''45'cong'737'_1254 ::
  T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1254 v0
  = let v1 = d_'43''45'isMonoid_1236 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsNearSemiring._.identity
d_identity_1256 ::
  T_IsNearSemiring_1218 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1256 v0
  = coe d_identity_698 (coe d_'43''45'isMonoid_1236 (coe v0))
-- Algebra.Structures.IsNearSemiring._.identityʳ
d_identity'691'_1258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsNearSemiring_1218 -> AgdaAny -> AgdaAny
d_identity'691'_1258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_1258 v7
du_identity'691'_1258 ::
  T_IsNearSemiring_1218 -> AgdaAny -> AgdaAny
du_identity'691'_1258 v0
  = coe du_identity'691'_728 (coe d_'43''45'isMonoid_1236 (coe v0))
-- Algebra.Structures.IsNearSemiring._.identityˡ
d_identity'737'_1260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsNearSemiring_1218 -> AgdaAny -> AgdaAny
d_identity'737'_1260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_1260 v7
du_identity'737'_1260 ::
  T_IsNearSemiring_1218 -> AgdaAny -> AgdaAny
du_identity'737'_1260 v0
  = coe du_identity'737'_726 (coe d_'43''45'isMonoid_1236 (coe v0))
-- Algebra.Structures.IsNearSemiring._.isMagma
d_isMagma_1262 :: T_IsNearSemiring_1218 -> T_IsMagma_176
d_isMagma_1262 v0
  = coe
      d_isMagma_480
      (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_1236 (coe v0)))
-- Algebra.Structures.IsNearSemiring._.isSemigroup
d_isSemigroup_1264 :: T_IsNearSemiring_1218 -> T_IsSemigroup_472
d_isSemigroup_1264 v0
  = coe d_isSemigroup_696 (coe d_'43''45'isMonoid_1236 (coe v0))
-- Algebra.Structures.IsNearSemiring._.isUnitalMagma
d_isUnitalMagma_1266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsNearSemiring_1218 -> T_IsUnitalMagma_642
d_isUnitalMagma_1266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isUnitalMagma_1266 v7
du_isUnitalMagma_1266 ::
  T_IsNearSemiring_1218 -> T_IsUnitalMagma_642
du_isUnitalMagma_1266 v0
  = coe du_isUnitalMagma_730 (coe d_'43''45'isMonoid_1236 (coe v0))
-- Algebra.Structures.IsNearSemiring._.isEquivalence
d_isEquivalence_1268 ::
  T_IsNearSemiring_1218 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1268 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_1236 (coe v0))))
-- Algebra.Structures.IsNearSemiring._.isPartialEquivalence
d_isPartialEquivalence_1270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1218 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1270 v7
du_isPartialEquivalence_1270 ::
  T_IsNearSemiring_1218 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1270 v0
  = let v1 = d_'43''45'isMonoid_1236 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.IsNearSemiring._.refl
d_refl_1272 :: T_IsNearSemiring_1218 -> AgdaAny -> AgdaAny
d_refl_1272 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_1236 (coe v0)))))
-- Algebra.Structures.IsNearSemiring._.reflexive
d_reflexive_1274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1218 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1274 v7
du_reflexive_1274 ::
  T_IsNearSemiring_1218 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1274 v0
  = let v1 = d_'43''45'isMonoid_1236 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_184 (coe v3)) v4)))
-- Algebra.Structures.IsNearSemiring._.setoid
d_setoid_1276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1218 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1276 v7
du_setoid_1276 ::
  T_IsNearSemiring_1218 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1276 v0
  = let v1 = d_'43''45'isMonoid_1236 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsNearSemiring._.sym
d_sym_1278 ::
  T_IsNearSemiring_1218 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1278 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_1236 (coe v0)))))
-- Algebra.Structures.IsNearSemiring._.trans
d_trans_1280 ::
  T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1280 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_1236 (coe v0)))))
-- Algebra.Structures.IsNearSemiring.*-isMagma
d_'42''45'isMagma_1282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsNearSemiring_1218 -> T_IsMagma_176
d_'42''45'isMagma_1282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagma_1282 v7
du_'42''45'isMagma_1282 :: T_IsNearSemiring_1218 -> T_IsMagma_176
du_'42''45'isMagma_1282 v0
  = coe
      C_IsMagma'46'constructor_1867
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_1236 (coe v0)))))
      (coe d_'42''45'cong_1238 (coe v0))
-- Algebra.Structures.IsNearSemiring.*-isSemigroup
d_'42''45'isSemigroup_1284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsNearSemiring_1218 -> T_IsSemigroup_472
d_'42''45'isSemigroup_1284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isSemigroup_1284 v7
du_'42''45'isSemigroup_1284 ::
  T_IsNearSemiring_1218 -> T_IsSemigroup_472
du_'42''45'isSemigroup_1284 v0
  = coe
      C_IsSemigroup'46'constructor_10417
      (coe du_'42''45'isMagma_1282 (coe v0))
      (coe d_'42''45'assoc_1240 (coe v0))
-- Algebra.Structures.IsNearSemiring._.∙-congʳ
d_'8729''45'cong'691'_1288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1288 v7
du_'8729''45'cong'691'_1288 ::
  T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1288 v0
  = coe
      du_'8729''45'cong'691'_206 (coe du_'42''45'isMagma_1282 (coe v0))
-- Algebra.Structures.IsNearSemiring._.∙-congˡ
d_'8729''45'cong'737'_1290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1290 v7
du_'8729''45'cong'737'_1290 ::
  T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1290 v0
  = coe
      du_'8729''45'cong'737'_202 (coe du_'42''45'isMagma_1282 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne
d_IsSemiringWithoutOne_1298 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemiringWithoutOne_1298
  = C_IsSemiringWithoutOne'46'constructor_37629 T_IsCommutativeMonoid_736
                                                (AgdaAny ->
                                                 AgdaAny ->
                                                 AgdaAny ->
                                                 AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                                (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                                MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                                MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1316 ::
  T_IsSemiringWithoutOne_1298 -> T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_1316 v0
  = case coe v0 of
      C_IsSemiringWithoutOne'46'constructor_37629 v1 v2 v3 v4 v5
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutOne.*-cong
d_'42''45'cong_1318 ::
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1318 v0
  = case coe v0 of
      C_IsSemiringWithoutOne'46'constructor_37629 v1 v2 v3 v4 v5
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutOne.*-assoc
d_'42''45'assoc_1320 ::
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1320 v0
  = case coe v0 of
      C_IsSemiringWithoutOne'46'constructor_37629 v1 v2 v3 v4 v5
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutOne.distrib
d_distrib_1322 ::
  T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1322 v0
  = case coe v0 of
      C_IsSemiringWithoutOne'46'constructor_37629 v1 v2 v3 v4 v5
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutOne.zero
d_zero_1324 ::
  T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1324 v0
  = case coe v0 of
      C_IsSemiringWithoutOne'46'constructor_37629 v1 v2 v3 v4 v5
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutOne._.comm
d_comm_1328 ::
  T_IsSemiringWithoutOne_1298 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_1328 v0
  = coe d_comm_748 (coe d_'43''45'isCommutativeMonoid_1316 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne._.isCommutativeMagma
d_isCommutativeMagma_1330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1298 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_1330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMagma_1330 v7
du_isCommutativeMagma_1330 ::
  T_IsSemiringWithoutOne_1298 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_1330 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1316 (coe v0) in
    coe
      (coe
         du_isCommutativeMagma_586
         (coe du_isCommutativeSemigroup_786 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutOne._.isCommutativeSemigroup
d_isCommutativeSemigroup_1332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1298 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_1332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeSemigroup_1332 v7
du_isCommutativeSemigroup_1332 ::
  T_IsSemiringWithoutOne_1298 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_1332 v0
  = coe
      du_isCommutativeSemigroup_786
      (coe d_'43''45'isCommutativeMonoid_1316 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne._.isMonoid
d_isMonoid_1334 :: T_IsSemiringWithoutOne_1298 -> T_IsMonoid_686
d_isMonoid_1334 v0
  = coe
      d_isMonoid_746 (coe d_'43''45'isCommutativeMonoid_1316 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne._.setoid
d_setoid_1336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1336 v7
du_setoid_1336 ::
  T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1336 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1316 (coe v0) in
    coe
      (let v2 = d_isMonoid_746 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsSemiringWithoutOne._._≈_
d__'8776'__1340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1298 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1340 = erased
-- Algebra.Structures.IsSemiringWithoutOne._._≉_
d__'8777'__1342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1298 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1342 = erased
-- Algebra.Structures.IsSemiringWithoutOne._.Carrier
d_Carrier_1344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1298 -> ()
d_Carrier_1344 = erased
-- Algebra.Structures.IsSemiringWithoutOne._.isEquivalence
d_isEquivalence_1346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isEquivalence_1346 v7
du_isEquivalence_1346 ::
  T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1346 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
      (let v1
             = d_isMonoid_746
                 (coe d_'43''45'isCommutativeMonoid_1316 (coe v0)) in
       coe
         (let v2 = d_isSemigroup_696 (coe v1) in
          coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2)))))
-- Algebra.Structures.IsSemiringWithoutOne._.isPartialEquivalence
d_isPartialEquivalence_1348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1348 v7
du_isPartialEquivalence_1348 ::
  T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1348 v0
  = let v1
          = let v1
                  = d_isMonoid_746
                      (coe d_'43''45'isCommutativeMonoid_1316 (coe v0)) in
            coe
              (let v2 = d_isSemigroup_696 (coe v1) in
               coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2)))) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutOne._.partialSetoid
d_partialSetoid_1350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_partialSetoid_1350 v7
du_partialSetoid_1350 ::
  T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1350 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
      (let v1
             = d_isMonoid_746
                 (coe d_'43''45'isCommutativeMonoid_1316 (coe v0)) in
       coe
         (let v2 = d_isSemigroup_696 (coe v1) in
          coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2)))))
-- Algebra.Structures.IsSemiringWithoutOne._.refl
d_refl_1352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1298 -> AgdaAny -> AgdaAny
d_refl_1352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_1352 v7
du_refl_1352 :: T_IsSemiringWithoutOne_1298 -> AgdaAny -> AgdaAny
du_refl_1352 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
         (let v1
                = d_isMonoid_746
                    (coe d_'43''45'isCommutativeMonoid_1316 (coe v0)) in
          coe
            (let v2 = d_isSemigroup_696 (coe v1) in
             coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2))))))
-- Algebra.Structures.IsSemiringWithoutOne._.reflexive
d_reflexive_1354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1354 v7
du_reflexive_1354 ::
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1354 v0
  = let v1
          = let v1
                  = d_isMonoid_746
                      (coe d_'43''45'isCommutativeMonoid_1316 (coe v0)) in
            coe
              (let v2 = d_isSemigroup_696 (coe v1) in
               coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2)))) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
           v2)
-- Algebra.Structures.IsSemiringWithoutOne._.sym
d_sym_1356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sym_1356 v7
du_sym_1356 ::
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1356 v0
  = let v1
          = let v1
                  = d_isMonoid_746
                      (coe d_'43''45'isCommutativeMonoid_1316 (coe v0)) in
            coe
              (let v2 = d_isSemigroup_696 (coe v1) in
               coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2)))) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutOne._.trans
d_trans_1358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_trans_1358 v7
du_trans_1358 ::
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1358 v0
  = let v1
          = let v1
                  = d_isMonoid_746
                      (coe d_'43''45'isCommutativeMonoid_1316 (coe v0)) in
            coe
              (let v2 = d_isSemigroup_696 (coe v1) in
               coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2)))) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutOne.*-isMagma
d_'42''45'isMagma_1360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1298 -> T_IsMagma_176
d_'42''45'isMagma_1360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagma_1360 v7
du_'42''45'isMagma_1360 ::
  T_IsSemiringWithoutOne_1298 -> T_IsMagma_176
du_'42''45'isMagma_1360 v0
  = coe
      C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
         (let v1
                = d_isSemigroup_696
                    (coe
                       d_isMonoid_746
                       (coe d_'43''45'isCommutativeMonoid_1316 (coe v0))) in
          coe (coe du_setoid_200 (coe d_isMagma_480 (coe v1)))))
      (coe d_'42''45'cong_1318 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_1362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1298 -> T_IsSemigroup_472
d_'42''45'isSemigroup_1362 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isSemigroup_1362 v7
du_'42''45'isSemigroup_1362 ::
  T_IsSemiringWithoutOne_1298 -> T_IsSemigroup_472
du_'42''45'isSemigroup_1362 v0
  = coe
      C_IsSemigroup'46'constructor_10417
      (coe du_'42''45'isMagma_1360 (coe v0))
      (coe d_'42''45'assoc_1320 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne._.∙-congʳ
d_'8729''45'cong'691'_1366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1366 v7
du_'8729''45'cong'691'_1366 ::
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1366 v0
  = coe
      du_'8729''45'cong'691'_206 (coe du_'42''45'isMagma_1360 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne._.∙-congˡ
d_'8729''45'cong'737'_1368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1368 v7
du_'8729''45'cong'737'_1368 ::
  T_IsSemiringWithoutOne_1298 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1368 v0
  = coe
      du_'8729''45'cong'737'_202 (coe du_'42''45'isMagma_1360 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne.zeroˡ
d_zero'737'_1370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1298 -> AgdaAny -> AgdaAny
d_zero'737'_1370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_zero'737'_1370 v7
du_zero'737'_1370 ::
  T_IsSemiringWithoutOne_1298 -> AgdaAny -> AgdaAny
du_zero'737'_1370 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_zero_1324 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne.zeroʳ
d_zero'691'_1372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1298 -> AgdaAny -> AgdaAny
d_zero'691'_1372 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_zero'691'_1372 v7
du_zero'691'_1372 ::
  T_IsSemiringWithoutOne_1298 -> AgdaAny -> AgdaAny
du_zero'691'_1372 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_zero_1324 (coe v0))
-- Algebra.Structures.IsSemiringWithoutOne.isNearSemiring
d_isNearSemiring_1374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsSemiringWithoutOne_1298 -> T_IsNearSemiring_1218
d_isNearSemiring_1374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiring_1374 v7
du_isNearSemiring_1374 ::
  T_IsSemiringWithoutOne_1298 -> T_IsNearSemiring_1218
du_isNearSemiring_1374 v0
  = coe
      C_IsNearSemiring'46'constructor_35025
      (coe
         d_isMonoid_746 (coe d_'43''45'isCommutativeMonoid_1316 (coe v0)))
      (coe d_'42''45'cong_1318 (coe v0))
      (coe d_'42''45'assoc_1320 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_distrib_1322 (coe v0)))
      (coe du_zero'737'_1370 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne
d_IsCommutativeSemiringWithoutOne_1382 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsCommutativeSemiringWithoutOne_1382
  = C_IsCommutativeSemiringWithoutOne'46'constructor_41457 T_IsSemiringWithoutOne_1298
                                                           (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeSemiringWithoutOne.isSemiringWithoutOne
d_isSemiringWithoutOne_1394 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  T_IsSemiringWithoutOne_1298
d_isSemiringWithoutOne_1394 v0
  = case coe v0 of
      C_IsCommutativeSemiringWithoutOne'46'constructor_41457 v1 v2
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemiringWithoutOne.*-comm
d_'42''45'comm_1396 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_1396 v0
  = case coe v0 of
      C_IsCommutativeSemiringWithoutOne'46'constructor_41457 v1 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._._≈_
d__'8776'__1400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1400 = erased
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._._≉_
d__'8777'__1402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1402 = erased
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.*-assoc
d_'42''45'assoc_1404 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1404 v0
  = coe
      d_'42''45'assoc_1320 (coe d_isSemiringWithoutOne_1394 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.*-cong
d_'42''45'cong_1406 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1406 v0
  = coe
      d_'42''45'cong_1318 (coe d_isSemiringWithoutOne_1394 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.∙-congʳ
d_'8729''45'cong'691'_1408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_1408 v7
du_'8729''45'cong'691'_1408 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1408 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (coe
         du_'8729''45'cong'691'_206 (coe du_'42''45'isMagma_1360 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.∙-congˡ
d_'8729''45'cong'737'_1410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_1410 v7
du_'8729''45'cong'737'_1410 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1410 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (coe
         du_'8729''45'cong'737'_202 (coe du_'42''45'isMagma_1360 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.*-isMagma
d_'42''45'isMagma_1412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeSemiringWithoutOne_1382 -> T_IsMagma_176
d_'42''45'isMagma_1412 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isMagma_1412 v7
du_'42''45'isMagma_1412 ::
  T_IsCommutativeSemiringWithoutOne_1382 -> T_IsMagma_176
du_'42''45'isMagma_1412 v0
  = coe
      du_'42''45'isMagma_1360 (coe d_isSemiringWithoutOne_1394 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.*-isSemigroup
d_'42''45'isSemigroup_1414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 -> T_IsSemigroup_472
d_'42''45'isSemigroup_1414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'42''45'isSemigroup_1414 v7
du_'42''45'isSemigroup_1414 ::
  T_IsCommutativeSemiringWithoutOne_1382 -> T_IsSemigroup_472
du_'42''45'isSemigroup_1414 v0
  = coe
      du_'42''45'isSemigroup_1362
      (coe d_isSemiringWithoutOne_1394 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.comm
d_comm_1416 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_1416 v0
  = coe
      d_comm_748
      (coe
         d_'43''45'isCommutativeMonoid_1316
         (coe d_isSemiringWithoutOne_1394 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isCommutativeMagma
d_isCommutativeMagma_1418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_1418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMagma_1418 v7
du_isCommutativeMagma_1418 ::
  T_IsCommutativeSemiringWithoutOne_1382 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_1418 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1316 (coe v1) in
       coe
         (coe
            du_isCommutativeMagma_586
            (coe du_isCommutativeSemigroup_786 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1420 ::
  T_IsCommutativeSemiringWithoutOne_1382 -> T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_1420 v0
  = coe
      d_'43''45'isCommutativeMonoid_1316
      (coe d_isSemiringWithoutOne_1394 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isCommutativeSemigroup
d_isCommutativeSemigroup_1422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 ->
  T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_1422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeSemigroup_1422 v7
du_isCommutativeSemigroup_1422 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_1422 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (coe
         du_isCommutativeSemigroup_786
         (coe d_'43''45'isCommutativeMonoid_1316 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isMonoid
d_isMonoid_1424 ::
  T_IsCommutativeSemiringWithoutOne_1382 -> T_IsMonoid_686
d_isMonoid_1424 v0
  = coe
      d_isMonoid_746
      (coe
         d_'43''45'isCommutativeMonoid_1316
         (coe d_isSemiringWithoutOne_1394 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.Carrier
d_Carrier_1426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeSemiringWithoutOne_1382 -> ()
d_Carrier_1426 = erased
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.distrib
d_distrib_1428 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1428 v0
  = coe d_distrib_1322 (coe d_isSemiringWithoutOne_1394 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isEquivalence
d_isEquivalence_1430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1430 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isEquivalence_1430 v7
du_isEquivalence_1430 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1430 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
         (let v2
                = d_isMonoid_746
                    (coe d_'43''45'isCommutativeMonoid_1316 (coe v1)) in
          coe
            (let v3 = d_isSemigroup_696 (coe v2) in
             coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isNearSemiring
d_isNearSemiring_1432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 -> T_IsNearSemiring_1218
d_isNearSemiring_1432 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiring_1432 v7
du_isNearSemiring_1432 ::
  T_IsCommutativeSemiringWithoutOne_1382 -> T_IsNearSemiring_1218
du_isNearSemiring_1432 v0
  = coe
      du_isNearSemiring_1374 (coe d_isSemiringWithoutOne_1394 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isPartialEquivalence
d_isPartialEquivalence_1434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1434 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_1434 v7
du_isPartialEquivalence_1434 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1434 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (let v2
             = let v2
                     = d_isMonoid_746
                         (coe d_'43''45'isCommutativeMonoid_1316 (coe v1)) in
               coe
                 (let v3 = d_isSemigroup_696 (coe v2) in
                  coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3)))) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.partialSetoid
d_partialSetoid_1436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_partialSetoid_1436 v7
du_partialSetoid_1436 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1436 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (let v2
                = d_isMonoid_746
                    (coe d_'43''45'isCommutativeMonoid_1316 (coe v1)) in
          coe
            (let v3 = d_isSemigroup_696 (coe v2) in
             coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.refl
d_refl_1438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 -> AgdaAny -> AgdaAny
d_refl_1438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_1438 v7
du_refl_1438 ::
  T_IsCommutativeSemiringWithoutOne_1382 -> AgdaAny -> AgdaAny
du_refl_1438 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
            (let v2
                   = d_isMonoid_746
                       (coe d_'43''45'isCommutativeMonoid_1316 (coe v1)) in
             coe
               (let v3 = d_isSemigroup_696 (coe v2) in
                coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3)))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.reflexive
d_reflexive_1440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_1440 v7
du_reflexive_1440 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1440 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (let v2
             = let v2
                     = d_isMonoid_746
                         (coe d_'43''45'isCommutativeMonoid_1316 (coe v1)) in
               coe
                 (let v3 = d_isSemigroup_696 (coe v2) in
                  coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3)))) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.setoid
d_setoid_1442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1442 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_1442 v7
du_setoid_1442 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1442 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1316 (coe v1) in
       coe
         (let v3 = d_isMonoid_746 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe (coe du_setoid_200 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.sym
d_sym_1444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sym_1444 v7
du_sym_1444 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1444 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (let v2
             = let v2
                     = d_isMonoid_746
                         (coe d_'43''45'isCommutativeMonoid_1316 (coe v1)) in
               coe
                 (let v3 = d_isSemigroup_696 (coe v2) in
                  coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3)))) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.trans
d_trans_1446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1446 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_trans_1446 v7
du_trans_1446 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1446 v0
  = let v1 = d_isSemiringWithoutOne_1394 (coe v0) in
    coe
      (let v2
             = let v2
                     = d_isMonoid_746
                         (coe d_'43''45'isCommutativeMonoid_1316 (coe v1)) in
               coe
                 (let v3 = d_isSemigroup_696 (coe v2) in
                  coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3)))) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.zero
d_zero_1448 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1448 v0
  = coe d_zero_1324 (coe d_isSemiringWithoutOne_1394 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.zeroʳ
d_zero'691'_1450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 -> AgdaAny -> AgdaAny
d_zero'691'_1450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_zero'691'_1450 v7
du_zero'691'_1450 ::
  T_IsCommutativeSemiringWithoutOne_1382 -> AgdaAny -> AgdaAny
du_zero'691'_1450 v0
  = coe du_zero'691'_1372 (coe d_isSemiringWithoutOne_1394 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.zeroˡ
d_zero'737'_1452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 -> AgdaAny -> AgdaAny
d_zero'737'_1452 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_zero'737'_1452 v7
du_zero'737'_1452 ::
  T_IsCommutativeSemiringWithoutOne_1382 -> AgdaAny -> AgdaAny
du_zero'737'_1452 v0
  = coe du_zero'737'_1370 (coe d_isSemiringWithoutOne_1394 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_1454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 ->
  T_IsCommutativeSemigroup_548
d_'42''45'isCommutativeSemigroup_1454 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      v7
  = du_'42''45'isCommutativeSemigroup_1454 v7
du_'42''45'isCommutativeSemigroup_1454 ::
  T_IsCommutativeSemiringWithoutOne_1382 ->
  T_IsCommutativeSemigroup_548
du_'42''45'isCommutativeSemigroup_1454 v0
  = coe
      C_IsCommutativeSemigroup'46'constructor_12093
      (coe
         du_'42''45'isSemigroup_1362
         (coe d_isSemiringWithoutOne_1394 (coe v0)))
      (coe d_'42''45'comm_1396 (coe v0))
-- Algebra.Structures.IsCommutativeSemiringWithoutOne._.isCommutativeMagma
d_isCommutativeMagma_1458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiringWithoutOne_1382 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_1458 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMagma_1458 v7
du_isCommutativeMagma_1458 ::
  T_IsCommutativeSemiringWithoutOne_1382 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_1458 v0
  = coe
      du_isCommutativeMagma_586
      (coe du_'42''45'isCommutativeSemigroup_1454 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_1468 a0 a1 a2 a3 a4 a5 a6 a7
  = ()
data T_IsSemiringWithoutAnnihilatingZero_1468
  = C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811 T_IsCommutativeMonoid_736
                                                             (AgdaAny ->
                                                              AgdaAny ->
                                                              AgdaAny ->
                                                              AgdaAny ->
                                                              AgdaAny -> AgdaAny -> AgdaAny)
                                                             (AgdaAny ->
                                                              AgdaAny -> AgdaAny -> AgdaAny)
                                                             MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                                             MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1488 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_1488 v0
  = case coe v0 of
      C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811 v1 v2 v3 v4 v5
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_1490 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1490 v0
  = case coe v0 of
      C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811 v1 v2 v3 v4 v5
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_1492 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1492 v0
  = case coe v0 of
      C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811 v1 v2 v3 v4 v5
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_1494 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1494 v0
  = case coe v0 of
      C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811 v1 v2 v3 v4 v5
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_1496 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1496 v0
  = case coe v0 of
      C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811 v1 v2 v3 v4 v5
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.distribˡ
d_distrib'737'_1498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1498 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_1498 v8
du_distrib'737'_1498 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1498 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_distrib_1496 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.distribʳ
d_distrib'691'_1500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1500 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_1500 v8
du_distrib'691'_1500 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1500 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_distrib_1496 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.assoc
d_assoc_1504 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1504 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746 (coe d_'43''45'isCommutativeMonoid_1488 (coe v0))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.comm
d_comm_1506 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_1506 v0
  = coe d_comm_748 (coe d_'43''45'isCommutativeMonoid_1488 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.∙-cong
d_'8729''45'cong_1508 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1508 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746 (coe d_'43''45'isCommutativeMonoid_1488 (coe v0)))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.∙-congʳ
d_'8729''45'cong'691'_1510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1510 v8
du_'8729''45'cong'691'_1510 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1510 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1488 (coe v0) in
    coe
      (let v2 = d_isMonoid_746 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.∙-congˡ
d_'8729''45'cong'737'_1512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1512 v8
du_'8729''45'cong'737'_1512 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1512 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1488 (coe v0) in
    coe
      (let v2 = d_isMonoid_746 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identity
d_identity_1514 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1514 v0
  = coe
      d_identity_698
      (coe
         d_isMonoid_746 (coe d_'43''45'isCommutativeMonoid_1488 (coe v0)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identityʳ
d_identity'691'_1516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 -> AgdaAny -> AgdaAny
d_identity'691'_1516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1516 v8
du_identity'691'_1516 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> AgdaAny -> AgdaAny
du_identity'691'_1516 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1488 (coe v0) in
    coe (coe du_identity'691'_728 (coe d_isMonoid_746 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identityˡ
d_identity'737'_1518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 -> AgdaAny -> AgdaAny
d_identity'737'_1518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1518 v8
du_identity'737'_1518 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> AgdaAny -> AgdaAny
du_identity'737'_1518 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1488 (coe v0) in
    coe (coe du_identity'737'_726 (coe d_isMonoid_746 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isCommutativeMagma
d_isCommutativeMagma_1520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  T_IsCommutativeMagma_212
d_isCommutativeMagma_1520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1520 v8
du_isCommutativeMagma_1520 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  T_IsCommutativeMagma_212
du_isCommutativeMagma_1520 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1488 (coe v0) in
    coe
      (coe
         du_isCommutativeMagma_586
         (coe du_isCommutativeSemigroup_786 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isCommutativeSemigroup
d_isCommutativeSemigroup_1522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_1522 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_1522 v8
du_isCommutativeSemigroup_1522 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_1522 v0
  = coe
      du_isCommutativeSemigroup_786
      (coe d_'43''45'isCommutativeMonoid_1488 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isMagma
d_isMagma_1524 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> T_IsMagma_176
d_isMagma_1524 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746 (coe d_'43''45'isCommutativeMonoid_1488 (coe v0))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isMonoid
d_isMonoid_1526 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> T_IsMonoid_686
d_isMonoid_1526 v0
  = coe
      d_isMonoid_746 (coe d_'43''45'isCommutativeMonoid_1488 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isSemigroup
d_isSemigroup_1528 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> T_IsSemigroup_472
d_isSemigroup_1528 v0
  = coe
      d_isSemigroup_696
      (coe
         d_isMonoid_746 (coe d_'43''45'isCommutativeMonoid_1488 (coe v0)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isUnitalMagma
d_isUnitalMagma_1530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 -> T_IsUnitalMagma_642
d_isUnitalMagma_1530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_1530 v8
du_isUnitalMagma_1530 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> T_IsUnitalMagma_642
du_isUnitalMagma_1530 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1488 (coe v0) in
    coe (coe du_isUnitalMagma_730 (coe d_isMonoid_746 (coe v1)))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isEquivalence
d_isEquivalence_1532 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1532 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746 (coe d_'43''45'isCommutativeMonoid_1488 (coe v0)))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.isPartialEquivalence
d_isPartialEquivalence_1534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1534 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1534 v8
du_isPartialEquivalence_1534 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1534 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1488 (coe v0) in
    coe
      (let v2 = d_isMonoid_746 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe
            (let v4 = d_isMagma_480 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe d_isEquivalence_184 (coe v4))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.refl
d_refl_1536 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> AgdaAny -> AgdaAny
d_refl_1536 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe d_'43''45'isCommutativeMonoid_1488 (coe v0))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.reflexive
d_reflexive_1538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1538 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1538 v8
du_reflexive_1538 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1538 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1488 (coe v0) in
    coe
      (let v2 = d_isMonoid_746 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe
            (let v4 = d_isMagma_480 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe d_isEquivalence_184 (coe v4)) v5))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.setoid
d_setoid_1540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1540 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1540 v8
du_setoid_1540 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1540 v0
  = let v1 = d_'43''45'isCommutativeMonoid_1488 (coe v0) in
    coe
      (let v2 = d_isMonoid_746 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.sym
d_sym_1542 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1542 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe d_'43''45'isCommutativeMonoid_1488 (coe v0))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.trans
d_trans_1544 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1544 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe d_'43''45'isCommutativeMonoid_1488 (coe v0))))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-isMagma
d_'42''45'isMagma_1546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 -> T_IsMagma_176
d_'42''45'isMagma_1546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_1546 v8
du_'42''45'isMagma_1546 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> T_IsMagma_176
du_'42''45'isMagma_1546 v0
  = coe
      C_IsMagma'46'constructor_1867
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe d_'43''45'isCommutativeMonoid_1488 (coe v0))))))
      (coe d_'42''45'cong_1490 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-isSemigroup
d_'42''45'isSemigroup_1548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 -> T_IsSemigroup_472
d_'42''45'isSemigroup_1548 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_1548 v8
du_'42''45'isSemigroup_1548 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> T_IsSemigroup_472
du_'42''45'isSemigroup_1548 v0
  = coe
      C_IsSemigroup'46'constructor_10417
      (coe du_'42''45'isMagma_1546 (coe v0))
      (coe d_'42''45'assoc_1492 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero.*-isMonoid
d_'42''45'isMonoid_1550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 -> T_IsMonoid_686
d_'42''45'isMonoid_1550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_1550 v8
du_'42''45'isMonoid_1550 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> T_IsMonoid_686
du_'42''45'isMonoid_1550 v0
  = coe
      C_IsMonoid'46'constructor_15873
      (coe du_'42''45'isSemigroup_1548 (coe v0))
      (coe d_'42''45'identity_1494 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.∙-congʳ
d_'8729''45'cong'691'_1554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1554 v8
du_'8729''45'cong'691'_1554 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1554 v0
  = let v1 = coe du_'42''45'isMonoid_1550 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.∙-congˡ
d_'8729''45'cong'737'_1556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1556 v8
du_'8729''45'cong'737'_1556 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1556 v0
  = let v1 = coe du_'42''45'isMonoid_1550 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identityʳ
d_identity'691'_1558 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 -> AgdaAny -> AgdaAny
d_identity'691'_1558 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1558 v8
du_identity'691'_1558 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> AgdaAny -> AgdaAny
du_identity'691'_1558 v0
  = coe du_identity'691'_728 (coe du_'42''45'isMonoid_1550 (coe v0))
-- Algebra.Structures.IsSemiringWithoutAnnihilatingZero._.identityˡ
d_identity'737'_1560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero_1468 -> AgdaAny -> AgdaAny
d_identity'737'_1560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1560 v8
du_identity'737'_1560 ::
  T_IsSemiringWithoutAnnihilatingZero_1468 -> AgdaAny -> AgdaAny
du_identity'737'_1560 v0
  = coe du_identity'737'_726 (coe du_'42''45'isMonoid_1550 (coe v0))
-- Algebra.Structures.IsSemiring
d_IsSemiring_1570 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsSemiring_1570
  = C_IsSemiring'46'constructor_48071 T_IsSemiringWithoutAnnihilatingZero_1468
                                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1584 ::
  T_IsSemiring_1570 -> T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_1584 v0
  = case coe v0 of
      C_IsSemiring'46'constructor_48071 v1 v2 -> coe v1
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiring.zero
d_zero_1586 ::
  T_IsSemiring_1570 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1586 v0
  = case coe v0 of
      C_IsSemiring'46'constructor_48071 v1 v2 -> coe v2
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsSemiring._.*-assoc
d_'42''45'assoc_1590 ::
  T_IsSemiring_1570 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1590 v0
  = coe
      d_'42''45'assoc_1492
      (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))
-- Algebra.Structures.IsSemiring._.*-cong
d_'42''45'cong_1592 ::
  T_IsSemiring_1570 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1592 v0
  = coe
      d_'42''45'cong_1490
      (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))
-- Algebra.Structures.IsSemiring._.∙-congʳ
d_'8729''45'cong'691'_1594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1570 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1594 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1594 v8
du_'8729''45'cong'691'_1594 ::
  T_IsSemiring_1570 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1594 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isMonoid_1550 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsSemiring._.∙-congˡ
d_'8729''45'cong'737'_1596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1570 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1596 v8
du_'8729''45'cong'737'_1596 ::
  T_IsSemiring_1570 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1596 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isMonoid_1550 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsSemiring._.*-identity
d_'42''45'identity_1598 ::
  T_IsSemiring_1570 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1598 v0
  = coe
      d_'42''45'identity_1494
      (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))
-- Algebra.Structures.IsSemiring._.identityʳ
d_identity'691'_1600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> AgdaAny -> AgdaAny
d_identity'691'_1600 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1600 v8
du_identity'691'_1600 :: T_IsSemiring_1570 -> AgdaAny -> AgdaAny
du_identity'691'_1600 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (coe du_identity'691'_728 (coe du_'42''45'isMonoid_1550 (coe v1)))
-- Algebra.Structures.IsSemiring._.identityˡ
d_identity'737'_1602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> AgdaAny -> AgdaAny
d_identity'737'_1602 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1602 v8
du_identity'737'_1602 :: T_IsSemiring_1570 -> AgdaAny -> AgdaAny
du_identity'737'_1602 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (coe du_identity'737'_726 (coe du_'42''45'isMonoid_1550 (coe v1)))
-- Algebra.Structures.IsSemiring._.*-isMagma
d_'42''45'isMagma_1604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> T_IsMagma_176
d_'42''45'isMagma_1604 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_1604 v8
du_'42''45'isMagma_1604 :: T_IsSemiring_1570 -> T_IsMagma_176
du_'42''45'isMagma_1604 v0
  = coe
      du_'42''45'isMagma_1546
      (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))
-- Algebra.Structures.IsSemiring._.*-isMonoid
d_'42''45'isMonoid_1606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> T_IsMonoid_686
d_'42''45'isMonoid_1606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_1606 v8
du_'42''45'isMonoid_1606 :: T_IsSemiring_1570 -> T_IsMonoid_686
du_'42''45'isMonoid_1606 v0
  = coe
      du_'42''45'isMonoid_1550
      (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))
-- Algebra.Structures.IsSemiring._.*-isSemigroup
d_'42''45'isSemigroup_1608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> T_IsSemigroup_472
d_'42''45'isSemigroup_1608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_1608 v8
du_'42''45'isSemigroup_1608 ::
  T_IsSemiring_1570 -> T_IsSemigroup_472
du_'42''45'isSemigroup_1608 v0
  = coe
      du_'42''45'isSemigroup_1548
      (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))
-- Algebra.Structures.IsSemiring._.assoc
d_assoc_1610 ::
  T_IsSemiring_1570 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1610 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746
            (coe
               d_'43''45'isCommutativeMonoid_1488
               (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0)))))
-- Algebra.Structures.IsSemiring._.comm
d_comm_1612 :: T_IsSemiring_1570 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_1612 v0
  = coe
      d_comm_748
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0)))
-- Algebra.Structures.IsSemiring._.∙-cong
d_'8729''45'cong_1614 ::
  T_IsSemiring_1570 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1614 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746
               (coe
                  d_'43''45'isCommutativeMonoid_1488
                  (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))))))
-- Algebra.Structures.IsSemiring._.∙-congʳ
d_'8729''45'cong'691'_1616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1570 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1616 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1616 v8
du_'8729''45'cong'691'_1616 ::
  T_IsSemiring_1570 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1616 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1488 (coe v1) in
       coe
         (let v3 = d_isMonoid_746 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsSemiring._.∙-congˡ
d_'8729''45'cong'737'_1618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1570 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1618 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1618 v8
du_'8729''45'cong'737'_1618 ::
  T_IsSemiring_1570 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1618 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1488 (coe v1) in
       coe
         (let v3 = d_isMonoid_746 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsSemiring._.identity
d_identity_1620 ::
  T_IsSemiring_1570 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1620 v0
  = coe
      d_identity_698
      (coe
         d_isMonoid_746
         (coe
            d_'43''45'isCommutativeMonoid_1488
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))))
-- Algebra.Structures.IsSemiring._.identityʳ
d_identity'691'_1622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> AgdaAny -> AgdaAny
d_identity'691'_1622 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1622 v8
du_identity'691'_1622 :: T_IsSemiring_1570 -> AgdaAny -> AgdaAny
du_identity'691'_1622 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1488 (coe v1) in
       coe (coe du_identity'691'_728 (coe d_isMonoid_746 (coe v2))))
-- Algebra.Structures.IsSemiring._.identityˡ
d_identity'737'_1624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> AgdaAny -> AgdaAny
d_identity'737'_1624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1624 v8
du_identity'737'_1624 :: T_IsSemiring_1570 -> AgdaAny -> AgdaAny
du_identity'737'_1624 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1488 (coe v1) in
       coe (coe du_identity'737'_726 (coe d_isMonoid_746 (coe v2))))
-- Algebra.Structures.IsSemiring._.isCommutativeMagma
d_isCommutativeMagma_1626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_1626 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1626 v8
du_isCommutativeMagma_1626 ::
  T_IsSemiring_1570 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_1626 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1488 (coe v1) in
       coe
         (coe
            du_isCommutativeMagma_586
            (coe du_isCommutativeSemigroup_786 (coe v2))))
-- Algebra.Structures.IsSemiring._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1628 ::
  T_IsSemiring_1570 -> T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_1628 v0
  = coe
      d_'43''45'isCommutativeMonoid_1488
      (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))
-- Algebra.Structures.IsSemiring._.isCommutativeSemigroup
d_isCommutativeSemigroup_1630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsSemiring_1570 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_1630 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_1630 v8
du_isCommutativeSemigroup_1630 ::
  T_IsSemiring_1570 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_1630 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (coe
         du_isCommutativeSemigroup_786
         (coe d_'43''45'isCommutativeMonoid_1488 (coe v1)))
-- Algebra.Structures.IsSemiring._.isMagma
d_isMagma_1632 :: T_IsSemiring_1570 -> T_IsMagma_176
d_isMagma_1632 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746
            (coe
               d_'43''45'isCommutativeMonoid_1488
               (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0)))))
-- Algebra.Structures.IsSemiring._.isMonoid
d_isMonoid_1634 :: T_IsSemiring_1570 -> T_IsMonoid_686
d_isMonoid_1634 v0
  = coe
      d_isMonoid_746
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0)))
-- Algebra.Structures.IsSemiring._.isSemigroup
d_isSemigroup_1636 :: T_IsSemiring_1570 -> T_IsSemigroup_472
d_isSemigroup_1636 v0
  = coe
      d_isSemigroup_696
      (coe
         d_isMonoid_746
         (coe
            d_'43''45'isCommutativeMonoid_1488
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))))
-- Algebra.Structures.IsSemiring._.isUnitalMagma
d_isUnitalMagma_1638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> T_IsUnitalMagma_642
d_isUnitalMagma_1638 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_1638 v8
du_isUnitalMagma_1638 :: T_IsSemiring_1570 -> T_IsUnitalMagma_642
du_isUnitalMagma_1638 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1488 (coe v1) in
       coe (coe du_isUnitalMagma_730 (coe d_isMonoid_746 (coe v2))))
-- Algebra.Structures.IsSemiring._.distrib
d_distrib_1640 ::
  T_IsSemiring_1570 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1640 v0
  = coe
      d_distrib_1496
      (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))
-- Algebra.Structures.IsSemiring._.distribʳ
d_distrib'691'_1642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1570 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1642 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_1642 v8
du_distrib'691'_1642 ::
  T_IsSemiring_1570 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1642 v0
  = coe
      du_distrib'691'_1500
      (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))
-- Algebra.Structures.IsSemiring._.distribˡ
d_distrib'737'_1644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1570 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1644 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_1644 v8
du_distrib'737'_1644 ::
  T_IsSemiring_1570 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1644 v0
  = coe
      du_distrib'737'_1498
      (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))
-- Algebra.Structures.IsSemiring._.isEquivalence
d_isEquivalence_1646 ::
  T_IsSemiring_1570 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1646 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746
               (coe
                  d_'43''45'isCommutativeMonoid_1488
                  (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0))))))
-- Algebra.Structures.IsSemiring._.isPartialEquivalence
d_isPartialEquivalence_1648 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1570 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1648 v8
du_isPartialEquivalence_1648 ::
  T_IsSemiring_1570 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1648 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1488 (coe v1) in
       coe
         (let v3 = d_isMonoid_746 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (let v5 = d_isMagma_480 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                     (coe d_isEquivalence_184 (coe v5)))))))
-- Algebra.Structures.IsSemiring._.refl
d_refl_1650 :: T_IsSemiring_1570 -> AgdaAny -> AgdaAny
d_refl_1650 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0)))))))
-- Algebra.Structures.IsSemiring._.reflexive
d_reflexive_1652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1570 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1652 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1652 v8
du_reflexive_1652 ::
  T_IsSemiring_1570 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1652 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1488 (coe v1) in
       coe
         (let v3 = d_isMonoid_746 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (let v5 = d_isMagma_480 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                       (coe d_isEquivalence_184 (coe v5)) v6)))))
-- Algebra.Structures.IsSemiring._.setoid
d_setoid_1654 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiring_1570 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1654 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1654 v8
du_setoid_1654 ::
  T_IsSemiring_1570 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1654 v0
  = let v1 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v0) in
    coe
      (let v2 = d_'43''45'isCommutativeMonoid_1488 (coe v1) in
       coe
         (let v3 = d_isMonoid_746 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe (coe du_setoid_200 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsSemiring._.sym
d_sym_1656 ::
  T_IsSemiring_1570 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1656 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0)))))))
-- Algebra.Structures.IsSemiring._.trans
d_trans_1658 ::
  T_IsSemiring_1570 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1658 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0)))))))
-- Algebra.Structures.IsSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_1660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsSemiring_1570 -> T_IsSemiringWithoutOne_1298
d_isSemiringWithoutOne_1660 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isSemiringWithoutOne_1660 v8
du_isSemiringWithoutOne_1660 ::
  T_IsSemiring_1570 -> T_IsSemiringWithoutOne_1298
du_isSemiringWithoutOne_1660 v0
  = coe
      C_IsSemiringWithoutOne'46'constructor_37629
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0)))
      (coe
         d_'42''45'cong_1490
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0)))
      (coe
         d_'42''45'assoc_1492
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0)))
      (coe
         d_distrib_1496
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v0)))
      (coe d_zero_1586 (coe v0))
-- Algebra.Structures.IsSemiring._.isNearSemiring
d_isNearSemiring_1664 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> T_IsNearSemiring_1218
d_isNearSemiring_1664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isNearSemiring_1664 v8
du_isNearSemiring_1664 ::
  T_IsSemiring_1570 -> T_IsNearSemiring_1218
du_isNearSemiring_1664 v0
  = coe
      du_isNearSemiring_1374 (coe du_isSemiringWithoutOne_1660 (coe v0))
-- Algebra.Structures.IsSemiring._.zeroʳ
d_zero'691'_1666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> AgdaAny -> AgdaAny
d_zero'691'_1666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'691'_1666 v8
du_zero'691'_1666 :: T_IsSemiring_1570 -> AgdaAny -> AgdaAny
du_zero'691'_1666 v0
  = coe du_zero'691'_1372 (coe du_isSemiringWithoutOne_1660 (coe v0))
-- Algebra.Structures.IsSemiring._.zeroˡ
d_zero'737'_1668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsSemiring_1570 -> AgdaAny -> AgdaAny
d_zero'737'_1668 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'737'_1668 v8
du_zero'737'_1668 :: T_IsSemiring_1570 -> AgdaAny -> AgdaAny
du_zero'737'_1668 v0
  = coe du_zero'737'_1370 (coe du_isSemiringWithoutOne_1660 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring
d_IsCommutativeSemiring_1678 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsCommutativeSemiring_1678
  = C_IsCommutativeSemiring'46'constructor_51895 T_IsSemiring_1570
                                                 (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeSemiring.isSemiring
d_isSemiring_1692 ::
  T_IsCommutativeSemiring_1678 -> T_IsSemiring_1570
d_isSemiring_1692 v0
  = case coe v0 of
      C_IsCommutativeSemiring'46'constructor_51895 v1 v2 -> coe v1
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemiring.*-comm
d_'42''45'comm_1694 ::
  T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_1694 v0
  = case coe v0 of
      C_IsCommutativeSemiring'46'constructor_51895 v1 v2 -> coe v2
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeSemiring._.*-assoc
d_'42''45'assoc_1698 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1698 v0
  = coe
      d_'42''45'assoc_1492
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1692 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiring._.*-cong
d_'42''45'cong_1700 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1700 v0
  = coe
      d_'42''45'cong_1490
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1692 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiring._.∙-congʳ
d_'8729''45'cong'691'_1702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1702 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1702 v8
du_'8729''45'cong'691'_1702 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1702 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = coe du_'42''45'isMonoid_1550 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsCommutativeSemiring._.∙-congˡ
d_'8729''45'cong'737'_1704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1704 v8
du_'8729''45'cong'737'_1704 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1704 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = coe du_'42''45'isMonoid_1550 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsCommutativeSemiring._.*-identity
d_'42''45'identity_1706 ::
  T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1706 v0
  = coe
      d_'42''45'identity_1494
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1692 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiring._.identityʳ
d_identity'691'_1708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
d_identity'691'_1708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1708 v8
du_identity'691'_1708 ::
  T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
du_identity'691'_1708 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (coe du_identity'691'_728 (coe du_'42''45'isMonoid_1550 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiring._.identityˡ
d_identity'737'_1710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
d_identity'737'_1710 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1710 v8
du_identity'737'_1710 ::
  T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
du_identity'737'_1710 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (coe du_identity'737'_726 (coe du_'42''45'isMonoid_1550 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiring._.*-isMagma
d_'42''45'isMagma_1712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeSemiring_1678 -> T_IsMagma_176
d_'42''45'isMagma_1712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_1712 v8
du_'42''45'isMagma_1712 ::
  T_IsCommutativeSemiring_1678 -> T_IsMagma_176
du_'42''45'isMagma_1712 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (coe
         du_'42''45'isMagma_1546
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.*-isMonoid
d_'42''45'isMonoid_1714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> T_IsMonoid_686
d_'42''45'isMonoid_1714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_1714 v8
du_'42''45'isMonoid_1714 ::
  T_IsCommutativeSemiring_1678 -> T_IsMonoid_686
du_'42''45'isMonoid_1714 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoid_1550
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.*-isSemigroup
d_'42''45'isSemigroup_1716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> T_IsSemigroup_472
d_'42''45'isSemigroup_1716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_1716 v8
du_'42''45'isSemigroup_1716 ::
  T_IsCommutativeSemiring_1678 -> T_IsSemigroup_472
du_'42''45'isSemigroup_1716 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (coe
         du_'42''45'isSemigroup_1548
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.assoc
d_assoc_1718 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1718 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746
            (coe
               d_'43''45'isCommutativeMonoid_1488
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1584
                  (coe d_isSemiring_1692 (coe v0))))))
-- Algebra.Structures.IsCommutativeSemiring._.comm
d_comm_1720 ::
  T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_1720 v0
  = coe
      d_comm_748
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe
            d_isSemiringWithoutAnnihilatingZero_1584
            (coe d_isSemiring_1692 (coe v0))))
-- Algebra.Structures.IsCommutativeSemiring._.∙-cong
d_'8729''45'cong_1722 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1722 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746
               (coe
                  d_'43''45'isCommutativeMonoid_1488
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1584
                     (coe d_isSemiring_1692 (coe v0)))))))
-- Algebra.Structures.IsCommutativeSemiring._.∙-congʳ
d_'8729''45'cong'691'_1724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1724 v8
du_'8729''45'cong'691'_1724 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1724 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (let v4 = d_isMonoid_746 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsCommutativeSemiring._.∙-congˡ
d_'8729''45'cong'737'_1726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1726 v8
du_'8729''45'cong'737'_1726 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1726 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (let v4 = d_isMonoid_746 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsCommutativeSemiring._.identity
d_identity_1728 ::
  T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1728 v0
  = coe
      d_identity_698
      (coe
         d_isMonoid_746
         (coe
            d_'43''45'isCommutativeMonoid_1488
            (coe
               d_isSemiringWithoutAnnihilatingZero_1584
               (coe d_isSemiring_1692 (coe v0)))))
-- Algebra.Structures.IsCommutativeSemiring._.identityʳ
d_identity'691'_1730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
d_identity'691'_1730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1730 v8
du_identity'691'_1730 ::
  T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
du_identity'691'_1730 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe (coe du_identity'691'_728 (coe d_isMonoid_746 (coe v3)))))
-- Algebra.Structures.IsCommutativeSemiring._.identityˡ
d_identity'737'_1732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
d_identity'737'_1732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1732 v8
du_identity'737'_1732 ::
  T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
du_identity'737'_1732 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe (coe du_identity'737'_726 (coe d_isMonoid_746 (coe v3)))))
-- Algebra.Structures.IsCommutativeSemiring._.isCommutativeMagma
d_isCommutativeMagma_1734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_1734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1734 v8
du_isCommutativeMagma_1734 ::
  T_IsCommutativeSemiring_1678 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_1734 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (coe
               du_isCommutativeMagma_586
               (coe du_isCommutativeSemigroup_786 (coe v3)))))
-- Algebra.Structures.IsCommutativeSemiring._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1736 ::
  T_IsCommutativeSemiring_1678 -> T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_1736 v0
  = coe
      d_'43''45'isCommutativeMonoid_1488
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1692 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiring._.isCommutativeSemigroup
d_isCommutativeSemigroup_1738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_1738 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_1738 v8
du_isCommutativeSemigroup_1738 ::
  T_IsCommutativeSemiring_1678 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_1738 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (coe
            du_isCommutativeSemigroup_786
            (coe d_'43''45'isCommutativeMonoid_1488 (coe v2))))
-- Algebra.Structures.IsCommutativeSemiring._.isMagma
d_isMagma_1740 :: T_IsCommutativeSemiring_1678 -> T_IsMagma_176
d_isMagma_1740 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746
            (coe
               d_'43''45'isCommutativeMonoid_1488
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1584
                  (coe d_isSemiring_1692 (coe v0))))))
-- Algebra.Structures.IsCommutativeSemiring._.isMonoid
d_isMonoid_1742 :: T_IsCommutativeSemiring_1678 -> T_IsMonoid_686
d_isMonoid_1742 v0
  = coe
      d_isMonoid_746
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe
            d_isSemiringWithoutAnnihilatingZero_1584
            (coe d_isSemiring_1692 (coe v0))))
-- Algebra.Structures.IsCommutativeSemiring._.isSemigroup
d_isSemigroup_1744 ::
  T_IsCommutativeSemiring_1678 -> T_IsSemigroup_472
d_isSemigroup_1744 v0
  = coe
      d_isSemigroup_696
      (coe
         d_isMonoid_746
         (coe
            d_'43''45'isCommutativeMonoid_1488
            (coe
               d_isSemiringWithoutAnnihilatingZero_1584
               (coe d_isSemiring_1692 (coe v0)))))
-- Algebra.Structures.IsCommutativeSemiring._.isUnitalMagma
d_isUnitalMagma_1746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> T_IsUnitalMagma_642
d_isUnitalMagma_1746 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_1746 v8
du_isUnitalMagma_1746 ::
  T_IsCommutativeSemiring_1678 -> T_IsUnitalMagma_642
du_isUnitalMagma_1746 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe (coe du_isUnitalMagma_730 (coe d_isMonoid_746 (coe v3)))))
-- Algebra.Structures.IsCommutativeSemiring._.distrib
d_distrib_1748 ::
  T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1748 v0
  = coe
      d_distrib_1496
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1692 (coe v0)))
-- Algebra.Structures.IsCommutativeSemiring._.distribʳ
d_distrib'691'_1750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_1750 v8
du_distrib'691'_1750 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1750 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (coe
         du_distrib'691'_1500
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.distribˡ
d_distrib'737'_1752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_1752 v8
du_distrib'737'_1752 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1752 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (coe
         du_distrib'737'_1498
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.isEquivalence
d_isEquivalence_1754 ::
  T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1754 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746
               (coe
                  d_'43''45'isCommutativeMonoid_1488
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1584
                     (coe d_isSemiring_1692 (coe v0)))))))
-- Algebra.Structures.IsCommutativeSemiring._.isNearSemiring
d_isNearSemiring_1756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> T_IsNearSemiring_1218
d_isNearSemiring_1756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isNearSemiring_1756 v8
du_isNearSemiring_1756 ::
  T_IsCommutativeSemiring_1678 -> T_IsNearSemiring_1218
du_isNearSemiring_1756 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (coe
         du_isNearSemiring_1374 (coe du_isSemiringWithoutOne_1660 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.isPartialEquivalence
d_isPartialEquivalence_1758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1758 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1758 v8
du_isPartialEquivalence_1758 ::
  T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1758 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (let v4 = d_isMonoid_746 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (let v6 = d_isMagma_480 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                        (coe d_isEquivalence_184 (coe v6))))))))
-- Algebra.Structures.IsCommutativeSemiring._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1760 ::
  T_IsCommutativeSemiring_1678 ->
  T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_1760 v0
  = coe
      d_isSemiringWithoutAnnihilatingZero_1584
      (coe d_isSemiring_1692 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring._.isSemiringWithoutOne
d_isSemiringWithoutOne_1762 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 -> T_IsSemiringWithoutOne_1298
d_isSemiringWithoutOne_1762 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isSemiringWithoutOne_1762 v8
du_isSemiringWithoutOne_1762 ::
  T_IsCommutativeSemiring_1678 -> T_IsSemiringWithoutOne_1298
du_isSemiringWithoutOne_1762 v0
  = coe du_isSemiringWithoutOne_1660 (coe d_isSemiring_1692 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring._.refl
d_refl_1764 :: T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
d_refl_1764 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe d_isSemiring_1692 (coe v0))))))))
-- Algebra.Structures.IsCommutativeSemiring._.reflexive
d_reflexive_1766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1766 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1766 v8
du_reflexive_1766 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1766 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (let v4 = d_isMonoid_746 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (let v6 = d_isMagma_480 (coe v5) in
                   coe
                     (\ v7 v8 v9 ->
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                          (coe d_isEquivalence_184 (coe v6)) v7))))))
-- Algebra.Structures.IsCommutativeSemiring._.setoid
d_setoid_1768 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1768 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1768 v8
du_setoid_1768 ::
  T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1768 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (let v4 = d_isMonoid_746 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe (coe du_setoid_200 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsCommutativeSemiring._.sym
d_sym_1770 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1770 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe d_isSemiring_1692 (coe v0))))))))
-- Algebra.Structures.IsCommutativeSemiring._.trans
d_trans_1772 ::
  T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1772 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe d_isSemiring_1692 (coe v0))))))))
-- Algebra.Structures.IsCommutativeSemiring._.zero
d_zero_1774 ::
  T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1774 v0 = coe d_zero_1586 (coe d_isSemiring_1692 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring._.zeroʳ
d_zero'691'_1776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
d_zero'691'_1776 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'691'_1776 v8
du_zero'691'_1776 ::
  T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
du_zero'691'_1776 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (coe du_zero'691'_1372 (coe du_isSemiringWithoutOne_1660 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.zeroˡ
d_zero'737'_1778 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
d_zero'737'_1778 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'737'_1778 v8
du_zero'737'_1778 ::
  T_IsCommutativeSemiring_1678 -> AgdaAny -> AgdaAny
du_zero'737'_1778 v0
  = let v1 = d_isSemiring_1692 (coe v0) in
    coe
      (coe du_zero'737'_1370 (coe du_isSemiringWithoutOne_1660 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_1780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 ->
  T_IsCommutativeSemiringWithoutOne_1382
d_isCommutativeSemiringWithoutOne_1780 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 v8
  = du_isCommutativeSemiringWithoutOne_1780 v8
du_isCommutativeSemiringWithoutOne_1780 ::
  T_IsCommutativeSemiring_1678 ->
  T_IsCommutativeSemiringWithoutOne_1382
du_isCommutativeSemiringWithoutOne_1780 v0
  = coe
      C_IsCommutativeSemiringWithoutOne'46'constructor_41457
      (coe du_isSemiringWithoutOne_1660 (coe d_isSemiring_1692 (coe v0)))
      (coe d_'42''45'comm_1694 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring._.isCommutativeMagma
d_isCommutativeMagma_1784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeSemiring_1678 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_1784 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1784 v8
du_isCommutativeMagma_1784 ::
  T_IsCommutativeSemiring_1678 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_1784 v0
  = let v1 = coe du_isCommutativeSemiringWithoutOne_1780 (coe v0) in
    coe
      (coe
         du_isCommutativeMagma_586
         (coe du_'42''45'isCommutativeSemigroup_1454 (coe v1)))
-- Algebra.Structures.IsCommutativeSemiring._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_1786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 -> T_IsCommutativeSemigroup_548
d_'42''45'isCommutativeSemigroup_1786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 v8
  = du_'42''45'isCommutativeSemigroup_1786 v8
du_'42''45'isCommutativeSemigroup_1786 ::
  T_IsCommutativeSemiring_1678 -> T_IsCommutativeSemigroup_548
du_'42''45'isCommutativeSemigroup_1786 v0
  = coe
      du_'42''45'isCommutativeSemigroup_1454
      (coe du_isCommutativeSemiringWithoutOne_1780 (coe v0))
-- Algebra.Structures.IsCommutativeSemiring.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_1788 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring_1678 -> T_IsCommutativeMonoid_736
d_'42''45'isCommutativeMonoid_1788 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   v8
  = du_'42''45'isCommutativeMonoid_1788 v8
du_'42''45'isCommutativeMonoid_1788 ::
  T_IsCommutativeSemiring_1678 -> T_IsCommutativeMonoid_736
du_'42''45'isCommutativeMonoid_1788 v0
  = coe
      C_IsCommutativeMonoid'46'constructor_17695
      (coe
         du_'42''45'isMonoid_1550
         (coe
            d_isSemiringWithoutAnnihilatingZero_1584
            (coe d_isSemiring_1692 (coe v0))))
      (coe d_'42''45'comm_1694 (coe v0))
-- Algebra.Structures.IsCancellativeCommutativeSemiring
d_IsCancellativeCommutativeSemiring_1798 a0 a1 a2 a3 a4 a5 a6 a7
  = ()
data T_IsCancellativeCommutativeSemiring_1798
  = C_IsCancellativeCommutativeSemiring'46'constructor_55863 T_IsCommutativeSemiring_1678
                                                             (AgdaAny ->
                                                              AgdaAny ->
                                                              AgdaAny ->
                                                              (AgdaAny ->
                                                               MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
                                                              AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCancellativeCommutativeSemiring.isCommutativeSemiring
d_isCommutativeSemiring_1812 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeSemiring_1678
d_isCommutativeSemiring_1812 v0
  = case coe v0 of
      C_IsCancellativeCommutativeSemiring'46'constructor_55863 v1 v2
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCancellativeCommutativeSemiring.*-cancelˡ-nonZero
d_'42''45'cancel'737''45'nonZero_1814 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny
d_'42''45'cancel'737''45'nonZero_1814 v0
  = case coe v0 of
      C_IsCancellativeCommutativeSemiring'46'constructor_55863 v1 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-assoc
d_'42''45'assoc_1818 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1818 v0
  = coe
      d_'42''45'assoc_1492
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-comm
d_'42''45'comm_1820 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_1820 v0
  = coe
      d_'42''45'comm_1694 (coe d_isCommutativeSemiring_1812 (coe v0))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-cong
d_'42''45'cong_1822 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1822 v0
  = coe
      d_'42''45'cong_1490
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.∙-congʳ
d_'8729''45'cong'691'_1824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1824 v8
du_'8729''45'cong'691'_1824 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1824 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = coe du_'42''45'isMonoid_1550 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.∙-congˡ
d_'8729''45'cong'737'_1826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1826 v8
du_'8729''45'cong'737'_1826 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1826 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = coe du_'42''45'isMonoid_1550 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-identity
d_'42''45'identity_1828 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1828 v0
  = coe
      d_'42''45'identity_1494
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.identityʳ
d_identity'691'_1830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
d_identity'691'_1830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1830 v8
du_identity'691'_1830 ::
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
du_identity'691'_1830 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (coe
               du_identity'691'_728 (coe du_'42''45'isMonoid_1550 (coe v3)))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.identityˡ
d_identity'737'_1832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
d_identity'737'_1832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1832 v8
du_identity'737'_1832 ::
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
du_identity'737'_1832 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (coe
               du_identity'737'_726 (coe du_'42''45'isMonoid_1550 (coe v3)))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isCommutativeMagma
d_isCommutativeMagma_1834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeMagma_212
d_isCommutativeMagma_1834 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1834 v8
du_isCommutativeMagma_1834 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeMagma_212
du_isCommutativeMagma_1834 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = coe du_isCommutativeSemiringWithoutOne_1780 (coe v1) in
       coe
         (coe
            du_isCommutativeMagma_586
            (coe du_'42''45'isCommutativeSemigroup_1454 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_1836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeMonoid_736
d_'42''45'isCommutativeMonoid_1836 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   v8
  = du_'42''45'isCommutativeMonoid_1836 v8
du_'42''45'isCommutativeMonoid_1836 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeMonoid_736
du_'42''45'isCommutativeMonoid_1836 v0
  = coe
      du_'42''45'isCommutativeMonoid_1788
      (coe d_isCommutativeSemiring_1812 (coe v0))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_1838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeSemigroup_548
d_'42''45'isCommutativeSemigroup_1838 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 v8
  = du_'42''45'isCommutativeSemigroup_1838 v8
du_'42''45'isCommutativeSemigroup_1838 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeSemigroup_548
du_'42''45'isCommutativeSemigroup_1838 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (coe
         du_'42''45'isCommutativeSemigroup_1454
         (coe du_isCommutativeSemiringWithoutOne_1780 (coe v1)))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-isMagma
d_'42''45'isMagma_1840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsMagma_176
d_'42''45'isMagma_1840 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_1840 v8
du_'42''45'isMagma_1840 ::
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsMagma_176
du_'42''45'isMagma_1840 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (coe
            du_'42''45'isMagma_1546
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-isMonoid
d_'42''45'isMonoid_1842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsMonoid_686
d_'42''45'isMonoid_1842 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_1842 v8
du_'42''45'isMonoid_1842 ::
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsMonoid_686
du_'42''45'isMonoid_1842 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (coe
            du_'42''45'isMonoid_1550
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.*-isSemigroup
d_'42''45'isSemigroup_1844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsSemigroup_472
d_'42''45'isSemigroup_1844 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_1844 v8
du_'42''45'isSemigroup_1844 ::
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsSemigroup_472
du_'42''45'isSemigroup_1844 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (coe
            du_'42''45'isSemigroup_1548
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.assoc
d_assoc_1846 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1846 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746
            (coe
               d_'43''45'isCommutativeMonoid_1488
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0)))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.comm
d_comm_1848 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_1848 v0
  = coe
      d_comm_748
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe
            d_isSemiringWithoutAnnihilatingZero_1584
            (coe
               d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0)))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.∙-cong
d_'8729''45'cong_1850 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1850 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746
               (coe
                  d_'43''45'isCommutativeMonoid_1488
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.∙-congʳ
d_'8729''45'cong'691'_1852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1852 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1852 v8
du_'8729''45'cong'691'_1852 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1852 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (let v5 = d_isMonoid_746 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v6))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.∙-congˡ
d_'8729''45'cong'737'_1854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1854 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1854 v8
du_'8729''45'cong'737'_1854 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1854 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (let v5 = d_isMonoid_746 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v6))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.identity
d_identity_1856 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1856 v0
  = coe
      d_identity_698
      (coe
         d_isMonoid_746
         (coe
            d_'43''45'isCommutativeMonoid_1488
            (coe
               d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.identityʳ
d_identity'691'_1858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
d_identity'691'_1858 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1858 v8
du_identity'691'_1858 ::
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
du_identity'691'_1858 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe (coe du_identity'691'_728 (coe d_isMonoid_746 (coe v4))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.identityˡ
d_identity'737'_1860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
d_identity'737'_1860 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1860 v8
du_identity'737'_1860 ::
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
du_identity'737'_1860 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe (coe du_identity'737'_726 (coe d_isMonoid_746 (coe v4))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isCommutativeMagma
d_isCommutativeMagma_1862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeMagma_212
d_isCommutativeMagma_1862 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1862 v8
du_isCommutativeMagma_1862 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeMagma_212
du_isCommutativeMagma_1862 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (coe
                  du_isCommutativeMagma_586
                  (coe du_isCommutativeSemigroup_786 (coe v4))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1864 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_1864 v0
  = coe
      d_'43''45'isCommutativeMonoid_1488
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isCommutativeSemigroup
d_isCommutativeSemigroup_1866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_1866 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_1866 v8
du_isCommutativeSemigroup_1866 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_1866 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (coe
               du_isCommutativeSemigroup_786
               (coe d_'43''45'isCommutativeMonoid_1488 (coe v3)))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isMagma
d_isMagma_1868 ::
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsMagma_176
d_isMagma_1868 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746
            (coe
               d_'43''45'isCommutativeMonoid_1488
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0)))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isMonoid
d_isMonoid_1870 ::
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsMonoid_686
d_isMonoid_1870 v0
  = coe
      d_isMonoid_746
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe
            d_isSemiringWithoutAnnihilatingZero_1584
            (coe
               d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0)))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isSemigroup
d_isSemigroup_1872 ::
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsSemigroup_472
d_isSemigroup_1872 v0
  = coe
      d_isSemigroup_696
      (coe
         d_isMonoid_746
         (coe
            d_'43''45'isCommutativeMonoid_1488
            (coe
               d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isUnitalMagma
d_isUnitalMagma_1874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsUnitalMagma_642
d_isUnitalMagma_1874 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_1874 v8
du_isUnitalMagma_1874 ::
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsUnitalMagma_642
du_isUnitalMagma_1874 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe (coe du_isUnitalMagma_730 (coe d_isMonoid_746 (coe v4))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.distrib
d_distrib_1876 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1876 v0
  = coe
      d_distrib_1496
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.distribʳ
d_distrib'691'_1878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1878 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_1878 v8
du_distrib'691'_1878 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1878 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (coe
            du_distrib'691'_1500
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.distribˡ
d_distrib'737'_1880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1880 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_1880 v8
du_distrib'737'_1880 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1880 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (coe
            du_distrib'737'_1498
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_1882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeSemiringWithoutOne_1382
d_isCommutativeSemiringWithoutOne_1882 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 v8
  = du_isCommutativeSemiringWithoutOne_1882 v8
du_isCommutativeSemiringWithoutOne_1882 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsCommutativeSemiringWithoutOne_1382
du_isCommutativeSemiringWithoutOne_1882 v0
  = coe
      du_isCommutativeSemiringWithoutOne_1780
      (coe d_isCommutativeSemiring_1812 (coe v0))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isEquivalence
d_isEquivalence_1884 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1884 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746
               (coe
                  d_'43''45'isCommutativeMonoid_1488
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isNearSemiring
d_isNearSemiring_1886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsNearSemiring_1218
d_isNearSemiring_1886 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isNearSemiring_1886 v8
du_isNearSemiring_1886 ::
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsNearSemiring_1218
du_isNearSemiring_1886 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (coe
            du_isNearSemiring_1374
            (coe du_isSemiringWithoutOne_1660 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isPartialEquivalence
d_isPartialEquivalence_1888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1888 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1888 v8
du_isPartialEquivalence_1888 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1888 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (let v5 = d_isMonoid_746 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (let v7 = d_isMagma_480 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                           (coe d_isEquivalence_184 (coe v7)))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isSemiring
d_isSemiring_1890 ::
  T_IsCancellativeCommutativeSemiring_1798 -> T_IsSemiring_1570
d_isSemiring_1890 v0
  = coe d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1892 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_1892 v0
  = coe
      d_isSemiringWithoutAnnihilatingZero_1584
      (coe d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0)))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.isSemiringWithoutOne
d_isSemiringWithoutOne_1894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsSemiringWithoutOne_1298
d_isSemiringWithoutOne_1894 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isSemiringWithoutOne_1894 v8
du_isSemiringWithoutOne_1894 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  T_IsSemiringWithoutOne_1298
du_isSemiringWithoutOne_1894 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (coe du_isSemiringWithoutOne_1660 (coe d_isSemiring_1692 (coe v1)))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.refl
d_refl_1896 ::
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
d_refl_1896 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe
                           d_isSemiring_1692
                           (coe d_isCommutativeSemiring_1812 (coe v0)))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.reflexive
d_reflexive_1898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1898 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1898 v8
du_reflexive_1898 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1898 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (let v5 = d_isMonoid_746 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (let v7 = d_isMagma_480 (coe v6) in
                      coe
                        (\ v8 v9 v10 ->
                           coe
                             MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                             (coe d_isEquivalence_184 (coe v7)) v8)))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.setoid
d_setoid_1900 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1900 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1900 v8
du_setoid_1900 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1900 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (let v5 = d_isMonoid_746 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe (coe du_setoid_200 (coe d_isMagma_480 (coe v6))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.sym
d_sym_1902 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1902 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe
                           d_isSemiring_1692
                           (coe d_isCommutativeSemiring_1812 (coe v0)))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.trans
d_trans_1904 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1904 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe
                           d_isSemiring_1692
                           (coe d_isCommutativeSemiring_1812 (coe v0)))))))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.zero
d_zero_1906 ::
  T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1906 v0
  = coe
      d_zero_1586
      (coe d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v0)))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.zeroʳ
d_zero'691'_1908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
d_zero'691'_1908 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'691'_1908 v8
du_zero'691'_1908 ::
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
du_zero'691'_1908 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (coe
            du_zero'691'_1372 (coe du_isSemiringWithoutOne_1660 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring._.zeroˡ
d_zero'737'_1910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
d_zero'737'_1910 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'737'_1910 v8
du_zero'737'_1910 ::
  T_IsCancellativeCommutativeSemiring_1798 -> AgdaAny -> AgdaAny
du_zero'737'_1910 v0
  = let v1 = d_isCommutativeSemiring_1812 (coe v0) in
    coe
      (let v2 = d_isSemiring_1692 (coe v1) in
       coe
         (coe
            du_zero'737'_1370 (coe du_isSemiringWithoutOne_1660 (coe v2))))
-- Algebra.Structures.IsCancellativeCommutativeSemiring.*-cancelʳ-nonZero
d_'42''45'cancel'691''45'nonZero_1912 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny
d_'42''45'cancel'691''45'nonZero_1912 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
                                      ~v7 v8
  = du_'42''45'cancel'691''45'nonZero_1912 v5 v8
du_'42''45'cancel'691''45'nonZero_1912 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsCancellativeCommutativeSemiring_1798 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny
du_'42''45'cancel'691''45'nonZero_1912 v0 v1
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'almostCancel'737''8658'almostCancel'691'_380
      (let v2
             = d_isSemiring_1692 (coe d_isCommutativeSemiring_1812 (coe v1)) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (let v5 = d_isMonoid_746 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe (coe du_setoid_200 (coe d_isMagma_480 (coe v6))))))))
      (coe v0)
      (coe
         d_'42''45'comm_1694 (coe d_isCommutativeSemiring_1812 (coe v1)))
      (coe d_'42''45'cancel'737''45'nonZero_1814 (coe v1))
-- Algebra.Structures.IsIdempotentSemiring
d_IsIdempotentSemiring_1922 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsIdempotentSemiring_1922
  = C_IsIdempotentSemiring'46'constructor_60011 T_IsSemiring_1570
                                                (AgdaAny -> AgdaAny)
-- Algebra.Structures.IsIdempotentSemiring.isSemiring
d_isSemiring_1936 ::
  T_IsIdempotentSemiring_1922 -> T_IsSemiring_1570
d_isSemiring_1936 v0
  = case coe v0 of
      C_IsIdempotentSemiring'46'constructor_60011 v1 v2 -> coe v1
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentSemiring.+-idem
d_'43''45'idem_1938 ::
  T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
d_'43''45'idem_1938 v0
  = case coe v0 of
      C_IsIdempotentSemiring'46'constructor_60011 v1 v2 -> coe v2
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsIdempotentSemiring._.*-assoc
d_'42''45'assoc_1942 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1942 v0
  = coe
      d_'42''45'assoc_1492
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1936 (coe v0)))
-- Algebra.Structures.IsIdempotentSemiring._.*-cong
d_'42''45'cong_1944 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1944 v0
  = coe
      d_'42''45'cong_1490
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1936 (coe v0)))
-- Algebra.Structures.IsIdempotentSemiring._.∙-congʳ
d_'8729''45'cong'691'_1946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1946 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1946 v8
du_'8729''45'cong'691'_1946 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1946 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = coe du_'42''45'isMonoid_1550 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsIdempotentSemiring._.∙-congˡ
d_'8729''45'cong'737'_1948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1948 v8
du_'8729''45'cong'737'_1948 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1948 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = coe du_'42''45'isMonoid_1550 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsIdempotentSemiring._.*-identity
d_'42''45'identity_1950 ::
  T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1950 v0
  = coe
      d_'42''45'identity_1494
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1936 (coe v0)))
-- Algebra.Structures.IsIdempotentSemiring._.identityʳ
d_identity'691'_1952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
d_identity'691'_1952 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1952 v8
du_identity'691'_1952 ::
  T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
du_identity'691'_1952 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (coe du_identity'691'_728 (coe du_'42''45'isMonoid_1550 (coe v2))))
-- Algebra.Structures.IsIdempotentSemiring._.identityˡ
d_identity'737'_1954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
d_identity'737'_1954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1954 v8
du_identity'737'_1954 ::
  T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
du_identity'737'_1954 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (coe du_identity'737'_726 (coe du_'42''45'isMonoid_1550 (coe v2))))
-- Algebra.Structures.IsIdempotentSemiring._.*-isMagma
d_'42''45'isMagma_1956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsIdempotentSemiring_1922 -> T_IsMagma_176
d_'42''45'isMagma_1956 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_1956 v8
du_'42''45'isMagma_1956 ::
  T_IsIdempotentSemiring_1922 -> T_IsMagma_176
du_'42''45'isMagma_1956 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (coe
         du_'42''45'isMagma_1546
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.*-isMonoid
d_'42''45'isMonoid_1958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsIdempotentSemiring_1922 -> T_IsMonoid_686
d_'42''45'isMonoid_1958 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_1958 v8
du_'42''45'isMonoid_1958 ::
  T_IsIdempotentSemiring_1922 -> T_IsMonoid_686
du_'42''45'isMonoid_1958 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (coe
         du_'42''45'isMonoid_1550
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.*-isSemigroup
d_'42''45'isSemigroup_1960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> T_IsSemigroup_472
d_'42''45'isSemigroup_1960 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_1960 v8
du_'42''45'isSemigroup_1960 ::
  T_IsIdempotentSemiring_1922 -> T_IsSemigroup_472
du_'42''45'isSemigroup_1960 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (coe
         du_'42''45'isSemigroup_1548
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.assoc
d_assoc_1962 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_1962 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746
            (coe
               d_'43''45'isCommutativeMonoid_1488
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1584
                  (coe d_isSemiring_1936 (coe v0))))))
-- Algebra.Structures.IsIdempotentSemiring._.comm
d_comm_1964 ::
  T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_1964 v0
  = coe
      d_comm_748
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe
            d_isSemiringWithoutAnnihilatingZero_1584
            (coe d_isSemiring_1936 (coe v0))))
-- Algebra.Structures.IsIdempotentSemiring._.∙-cong
d_'8729''45'cong_1966 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1966 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746
               (coe
                  d_'43''45'isCommutativeMonoid_1488
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1584
                     (coe d_isSemiring_1936 (coe v0)))))))
-- Algebra.Structures.IsIdempotentSemiring._.∙-congʳ
d_'8729''45'cong'691'_1968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1968 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_1968 v8
du_'8729''45'cong'691'_1968 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1968 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (let v4 = d_isMonoid_746 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsIdempotentSemiring._.∙-congˡ
d_'8729''45'cong'737'_1970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1970 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_1970 v8
du_'8729''45'cong'737'_1970 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1970 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (let v4 = d_isMonoid_746 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsIdempotentSemiring._.identity
d_identity_1972 ::
  T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1972 v0
  = coe
      d_identity_698
      (coe
         d_isMonoid_746
         (coe
            d_'43''45'isCommutativeMonoid_1488
            (coe
               d_isSemiringWithoutAnnihilatingZero_1584
               (coe d_isSemiring_1936 (coe v0)))))
-- Algebra.Structures.IsIdempotentSemiring._.identityʳ
d_identity'691'_1974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
d_identity'691'_1974 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_1974 v8
du_identity'691'_1974 ::
  T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
du_identity'691'_1974 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe (coe du_identity'691'_728 (coe d_isMonoid_746 (coe v3)))))
-- Algebra.Structures.IsIdempotentSemiring._.identityˡ
d_identity'737'_1976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
d_identity'737'_1976 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_1976 v8
du_identity'737'_1976 ::
  T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
du_identity'737'_1976 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe (coe du_identity'737'_726 (coe d_isMonoid_746 (coe v3)))))
-- Algebra.Structures.IsIdempotentSemiring._.isCommutativeMagma
d_isCommutativeMagma_1978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_1978 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_1978 v8
du_isCommutativeMagma_1978 ::
  T_IsIdempotentSemiring_1922 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_1978 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (coe
               du_isCommutativeMagma_586
               (coe du_isCommutativeSemigroup_786 (coe v3)))))
-- Algebra.Structures.IsIdempotentSemiring._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1980 ::
  T_IsIdempotentSemiring_1922 -> T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_1980 v0
  = coe
      d_'43''45'isCommutativeMonoid_1488
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1936 (coe v0)))
-- Algebra.Structures.IsIdempotentSemiring._.isCommutativeSemigroup
d_isCommutativeSemigroup_1982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_1982 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_1982 v8
du_isCommutativeSemigroup_1982 ::
  T_IsIdempotentSemiring_1922 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_1982 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (coe
            du_isCommutativeSemigroup_786
            (coe d_'43''45'isCommutativeMonoid_1488 (coe v2))))
-- Algebra.Structures.IsIdempotentSemiring._.isMagma
d_isMagma_1984 :: T_IsIdempotentSemiring_1922 -> T_IsMagma_176
d_isMagma_1984 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746
            (coe
               d_'43''45'isCommutativeMonoid_1488
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1584
                  (coe d_isSemiring_1936 (coe v0))))))
-- Algebra.Structures.IsIdempotentSemiring._.isMonoid
d_isMonoid_1986 :: T_IsIdempotentSemiring_1922 -> T_IsMonoid_686
d_isMonoid_1986 v0
  = coe
      d_isMonoid_746
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe
            d_isSemiringWithoutAnnihilatingZero_1584
            (coe d_isSemiring_1936 (coe v0))))
-- Algebra.Structures.IsIdempotentSemiring._.isSemigroup
d_isSemigroup_1988 ::
  T_IsIdempotentSemiring_1922 -> T_IsSemigroup_472
d_isSemigroup_1988 v0
  = coe
      d_isSemigroup_696
      (coe
         d_isMonoid_746
         (coe
            d_'43''45'isCommutativeMonoid_1488
            (coe
               d_isSemiringWithoutAnnihilatingZero_1584
               (coe d_isSemiring_1936 (coe v0)))))
-- Algebra.Structures.IsIdempotentSemiring._.isUnitalMagma
d_isUnitalMagma_1990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> T_IsUnitalMagma_642
d_isUnitalMagma_1990 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_1990 v8
du_isUnitalMagma_1990 ::
  T_IsIdempotentSemiring_1922 -> T_IsUnitalMagma_642
du_isUnitalMagma_1990 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe (coe du_isUnitalMagma_730 (coe d_isMonoid_746 (coe v3)))))
-- Algebra.Structures.IsIdempotentSemiring._.distrib
d_distrib_1992 ::
  T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1992 v0
  = coe
      d_distrib_1496
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1936 (coe v0)))
-- Algebra.Structures.IsIdempotentSemiring._.distribʳ
d_distrib'691'_1994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1994 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_1994 v8
du_distrib'691'_1994 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_1994 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (coe
         du_distrib'691'_1500
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.distribˡ
d_distrib'737'_1996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_1996 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_1996 v8
du_distrib'737'_1996 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_1996 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (coe
         du_distrib'737'_1498
         (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.isEquivalence
d_isEquivalence_1998 ::
  T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1998 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746
               (coe
                  d_'43''45'isCommutativeMonoid_1488
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1584
                     (coe d_isSemiring_1936 (coe v0)))))))
-- Algebra.Structures.IsIdempotentSemiring._.isNearSemiring
d_isNearSemiring_2000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> T_IsNearSemiring_1218
d_isNearSemiring_2000 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isNearSemiring_2000 v8
du_isNearSemiring_2000 ::
  T_IsIdempotentSemiring_1922 -> T_IsNearSemiring_1218
du_isNearSemiring_2000 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (coe
         du_isNearSemiring_1374 (coe du_isSemiringWithoutOne_1660 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.isPartialEquivalence
d_isPartialEquivalence_2002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_2002 v8
du_isPartialEquivalence_2002 ::
  T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2002 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (let v4 = d_isMonoid_746 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (let v6 = d_isMagma_480 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                        (coe d_isEquivalence_184 (coe v6))))))))
-- Algebra.Structures.IsIdempotentSemiring._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2004 ::
  T_IsIdempotentSemiring_1922 ->
  T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_2004 v0
  = coe
      d_isSemiringWithoutAnnihilatingZero_1584
      (coe d_isSemiring_1936 (coe v0))
-- Algebra.Structures.IsIdempotentSemiring._.isSemiringWithoutOne
d_isSemiringWithoutOne_2006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 -> T_IsSemiringWithoutOne_1298
d_isSemiringWithoutOne_2006 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isSemiringWithoutOne_2006 v8
du_isSemiringWithoutOne_2006 ::
  T_IsIdempotentSemiring_1922 -> T_IsSemiringWithoutOne_1298
du_isSemiringWithoutOne_2006 v0
  = coe du_isSemiringWithoutOne_1660 (coe d_isSemiring_1936 (coe v0))
-- Algebra.Structures.IsIdempotentSemiring._.refl
d_refl_2008 :: T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
d_refl_2008 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe d_isSemiring_1936 (coe v0))))))))
-- Algebra.Structures.IsIdempotentSemiring._.reflexive
d_reflexive_2010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2010 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_2010 v8
du_reflexive_2010 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2010 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (let v4 = d_isMonoid_746 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (let v6 = d_isMagma_480 (coe v5) in
                   coe
                     (\ v7 v8 v9 ->
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                          (coe d_isEquivalence_184 (coe v6)) v7))))))
-- Algebra.Structures.IsIdempotentSemiring._.setoid
d_setoid_2012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2012 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_2012 v8
du_setoid_2012 ::
  T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2012 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (let v2 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v1) in
       coe
         (let v3 = d_'43''45'isCommutativeMonoid_1488 (coe v2) in
          coe
            (let v4 = d_isMonoid_746 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe (coe du_setoid_200 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsIdempotentSemiring._.sym
d_sym_2014 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2014 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe d_isSemiring_1936 (coe v0))))))))
-- Algebra.Structures.IsIdempotentSemiring._.trans
d_trans_2016 ::
  T_IsIdempotentSemiring_1922 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2016 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe d_isSemiring_1936 (coe v0))))))))
-- Algebra.Structures.IsIdempotentSemiring._.zero
d_zero_2018 ::
  T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2018 v0 = coe d_zero_1586 (coe d_isSemiring_1936 (coe v0))
-- Algebra.Structures.IsIdempotentSemiring._.zeroʳ
d_zero'691'_2020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
d_zero'691'_2020 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'691'_2020 v8
du_zero'691'_2020 ::
  T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
du_zero'691'_2020 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (coe du_zero'691'_1372 (coe du_isSemiringWithoutOne_1660 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.zeroˡ
d_zero'737'_2022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
d_zero'737'_2022 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'737'_2022 v8
du_zero'737'_2022 ::
  T_IsIdempotentSemiring_1922 -> AgdaAny -> AgdaAny
du_zero'737'_2022 v0
  = let v1 = d_isSemiring_1936 (coe v0) in
    coe
      (coe du_zero'737'_1370 (coe du_isSemiringWithoutOne_1660 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_2024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsIdempotentSemiring_1922 -> T_IsIdempotentCommutativeMonoid_852
d_'43''45'isIdempotentCommutativeMonoid_2024 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 ~v7 v8
  = du_'43''45'isIdempotentCommutativeMonoid_2024 v8
du_'43''45'isIdempotentCommutativeMonoid_2024 ::
  T_IsIdempotentSemiring_1922 -> T_IsIdempotentCommutativeMonoid_852
du_'43''45'isIdempotentCommutativeMonoid_2024 v0
  = coe
      C_IsIdempotentCommutativeMonoid'46'constructor_20685
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe
            d_isSemiringWithoutAnnihilatingZero_1584
            (coe d_isSemiring_1936 (coe v0))))
      (coe d_'43''45'idem_1938 (coe v0))
-- Algebra.Structures.IsIdempotentSemiring._.isBand
d_isBand_2028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsIdempotentSemiring_1922 -> T_IsBand_508
d_isBand_2028 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isBand_2028 v8
du_isBand_2028 :: T_IsIdempotentSemiring_1922 -> T_IsBand_508
du_isBand_2028 v0
  = let v1
          = coe du_'43''45'isIdempotentCommutativeMonoid_2024 (coe v0) in
    coe (coe du_isBand_846 (coe du_isIdempotentMonoid_910 (coe v1)))
-- Algebra.Structures.IsIdempotentSemiring._.isCommutativeBand
d_isCommutativeBand_2030 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> T_IsCommutativeBand_590
d_isCommutativeBand_2030 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeBand_2030 v8
du_isCommutativeBand_2030 ::
  T_IsIdempotentSemiring_1922 -> T_IsCommutativeBand_590
du_isCommutativeBand_2030 v0
  = coe
      du_isCommutativeBand_916
      (coe du_'43''45'isIdempotentCommutativeMonoid_2024 (coe v0))
-- Algebra.Structures.IsIdempotentSemiring._.isIdempotentMonoid
d_isIdempotentMonoid_2032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsIdempotentSemiring_1922 -> T_IsIdempotentMonoid_796
d_isIdempotentMonoid_2032 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isIdempotentMonoid_2032 v8
du_isIdempotentMonoid_2032 ::
  T_IsIdempotentSemiring_1922 -> T_IsIdempotentMonoid_796
du_isIdempotentMonoid_2032 v0
  = coe
      du_isIdempotentMonoid_910
      (coe du_'43''45'isIdempotentCommutativeMonoid_2024 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra
d_IsKleeneAlgebra_2044 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsKleeneAlgebra_2044
  = C_IsKleeneAlgebra'46'constructor_63875 T_IsIdempotentSemiring_1922
                                           MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                           MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsKleeneAlgebra.isIdempotentSemiring
d_isIdempotentSemiring_2062 ::
  T_IsKleeneAlgebra_2044 -> T_IsIdempotentSemiring_1922
d_isIdempotentSemiring_2062 v0
  = case coe v0 of
      C_IsKleeneAlgebra'46'constructor_63875 v1 v2 v3 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsKleeneAlgebra.starExpansive
d_starExpansive_2064 ::
  T_IsKleeneAlgebra_2044 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starExpansive_2064 v0
  = case coe v0 of
      C_IsKleeneAlgebra'46'constructor_63875 v1 v2 v3 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsKleeneAlgebra.starDestructive
d_starDestructive_2066 ::
  T_IsKleeneAlgebra_2044 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starDestructive_2066 v0
  = case coe v0 of
      C_IsKleeneAlgebra'46'constructor_63875 v1 v2 v3 -> coe v3
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsKleeneAlgebra._.*-assoc
d_'42''45'assoc_2070 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2070 v0
  = coe
      d_'42''45'assoc_1492
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0))))
-- Algebra.Structures.IsKleeneAlgebra._.*-cong
d_'42''45'cong_2072 ::
  T_IsKleeneAlgebra_2044 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2072 v0
  = coe
      d_'42''45'cong_1490
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0))))
-- Algebra.Structures.IsKleeneAlgebra._.∙-congʳ
d_'8729''45'cong'691'_2074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2074 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2074 v9
du_'8729''45'cong'691'_2074 ::
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2074 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = coe du_'42''45'isMonoid_1550 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsKleeneAlgebra._.∙-congˡ
d_'8729''45'cong'737'_2076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2076 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2076 v9
du_'8729''45'cong'737'_2076 ::
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2076 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = coe du_'42''45'isMonoid_1550 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsKleeneAlgebra._.*-identity
d_'42''45'identity_2078 ::
  T_IsKleeneAlgebra_2044 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2078 v0
  = coe
      d_'42''45'identity_1494
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0))))
-- Algebra.Structures.IsKleeneAlgebra._.identityʳ
d_identity'691'_2080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
d_identity'691'_2080 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2080 v9
du_identity'691'_2080 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
du_identity'691'_2080 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (coe
               du_identity'691'_728 (coe du_'42''45'isMonoid_1550 (coe v3)))))
-- Algebra.Structures.IsKleeneAlgebra._.identityˡ
d_identity'737'_2082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
d_identity'737'_2082 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2082 v9
du_identity'737'_2082 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
du_identity'737'_2082 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (coe
               du_identity'737'_726 (coe du_'42''45'isMonoid_1550 (coe v3)))))
-- Algebra.Structures.IsKleeneAlgebra._.*-isMagma
d_'42''45'isMagma_2084 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> T_IsMagma_176
d_'42''45'isMagma_2084 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMagma_2084 v9
du_'42''45'isMagma_2084 :: T_IsKleeneAlgebra_2044 -> T_IsMagma_176
du_'42''45'isMagma_2084 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (coe
            du_'42''45'isMagma_1546
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.*-isMonoid
d_'42''45'isMonoid_2086 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> T_IsMonoid_686
d_'42''45'isMonoid_2086 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMonoid_2086 v9
du_'42''45'isMonoid_2086 ::
  T_IsKleeneAlgebra_2044 -> T_IsMonoid_686
du_'42''45'isMonoid_2086 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (coe
            du_'42''45'isMonoid_1550
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.*-isSemigroup
d_'42''45'isSemigroup_2088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> T_IsSemigroup_472
d_'42''45'isSemigroup_2088 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isSemigroup_2088 v9
du_'42''45'isSemigroup_2088 ::
  T_IsKleeneAlgebra_2044 -> T_IsSemigroup_472
du_'42''45'isSemigroup_2088 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (coe
            du_'42''45'isSemigroup_1548
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.assoc
d_assoc_2090 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2090 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746
            (coe
               d_'43''45'isCommutativeMonoid_1488
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0)))))))
-- Algebra.Structures.IsKleeneAlgebra._.comm
d_comm_2092 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2092 v0
  = coe
      d_comm_748
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe
            d_isSemiringWithoutAnnihilatingZero_1584
            (coe
               d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0)))))
-- Algebra.Structures.IsKleeneAlgebra._.∙-cong
d_'8729''45'cong_2094 ::
  T_IsKleeneAlgebra_2044 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2094 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746
               (coe
                  d_'43''45'isCommutativeMonoid_1488
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0))))))))
-- Algebra.Structures.IsKleeneAlgebra._.∙-congʳ
d_'8729''45'cong'691'_2096 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2096 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2096 v9
du_'8729''45'cong'691'_2096 ::
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2096 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (let v5 = d_isMonoid_746 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v6))))))))
-- Algebra.Structures.IsKleeneAlgebra._.∙-congˡ
d_'8729''45'cong'737'_2098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2098 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2098 v9
du_'8729''45'cong'737'_2098 ::
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2098 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (let v5 = d_isMonoid_746 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v6))))))))
-- Algebra.Structures.IsKleeneAlgebra._.+-idem
d_'43''45'idem_2100 :: T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
d_'43''45'idem_2100 v0
  = coe
      d_'43''45'idem_1938 (coe d_isIdempotentSemiring_2062 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra._.identity
d_identity_2102 ::
  T_IsKleeneAlgebra_2044 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2102 v0
  = coe
      d_identity_698
      (coe
         d_isMonoid_746
         (coe
            d_'43''45'isCommutativeMonoid_1488
            (coe
               d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0))))))
-- Algebra.Structures.IsKleeneAlgebra._.identityʳ
d_identity'691'_2104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
d_identity'691'_2104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2104 v9
du_identity'691'_2104 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
du_identity'691'_2104 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe (coe du_identity'691'_728 (coe d_isMonoid_746 (coe v4))))))
-- Algebra.Structures.IsKleeneAlgebra._.identityˡ
d_identity'737'_2106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
d_identity'737'_2106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2106 v9
du_identity'737'_2106 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
du_identity'737'_2106 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe (coe du_identity'737'_726 (coe d_isMonoid_746 (coe v4))))))
-- Algebra.Structures.IsKleeneAlgebra._.isBand
d_isBand_2108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> T_IsBand_508
d_isBand_2108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isBand_2108 v9
du_isBand_2108 :: T_IsKleeneAlgebra_2044 -> T_IsBand_508
du_isBand_2108 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2
             = coe du_'43''45'isIdempotentCommutativeMonoid_2024 (coe v1) in
       coe (coe du_isBand_846 (coe du_isIdempotentMonoid_910 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.isCommutativeBand
d_isCommutativeBand_2110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2044 -> T_IsCommutativeBand_590
d_isCommutativeBand_2110 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeBand_2110 v9
du_isCommutativeBand_2110 ::
  T_IsKleeneAlgebra_2044 -> T_IsCommutativeBand_590
du_isCommutativeBand_2110 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (coe
         du_isCommutativeBand_916
         (coe du_'43''45'isIdempotentCommutativeMonoid_2024 (coe v1)))
-- Algebra.Structures.IsKleeneAlgebra._.isCommutativeMagma
d_isCommutativeMagma_2112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2044 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_2112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_2112 v9
du_isCommutativeMagma_2112 ::
  T_IsKleeneAlgebra_2044 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_2112 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (coe
                  du_isCommutativeMagma_586
                  (coe du_isCommutativeSemigroup_786 (coe v4))))))
-- Algebra.Structures.IsKleeneAlgebra._.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2114 ::
  T_IsKleeneAlgebra_2044 -> T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2114 v0
  = coe
      d_'43''45'isCommutativeMonoid_1488
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0))))
-- Algebra.Structures.IsKleeneAlgebra._.isCommutativeSemigroup
d_isCommutativeSemigroup_2116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2044 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_2116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              v9
  = du_isCommutativeSemigroup_2116 v9
du_isCommutativeSemigroup_2116 ::
  T_IsKleeneAlgebra_2044 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_2116 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (coe
               du_isCommutativeSemigroup_786
               (coe d_'43''45'isCommutativeMonoid_1488 (coe v3)))))
-- Algebra.Structures.IsKleeneAlgebra._.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_2118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 -> T_IsIdempotentCommutativeMonoid_852
d_'43''45'isIdempotentCommutativeMonoid_2118 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 ~v7 ~v8 v9
  = du_'43''45'isIdempotentCommutativeMonoid_2118 v9
du_'43''45'isIdempotentCommutativeMonoid_2118 ::
  T_IsKleeneAlgebra_2044 -> T_IsIdempotentCommutativeMonoid_852
du_'43''45'isIdempotentCommutativeMonoid_2118 v0
  = coe
      du_'43''45'isIdempotentCommutativeMonoid_2024
      (coe d_isIdempotentSemiring_2062 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra._.isIdempotentMonoid
d_isIdempotentMonoid_2120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2044 -> T_IsIdempotentMonoid_796
d_isIdempotentMonoid_2120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isIdempotentMonoid_2120 v9
du_isIdempotentMonoid_2120 ::
  T_IsKleeneAlgebra_2044 -> T_IsIdempotentMonoid_796
du_isIdempotentMonoid_2120 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (coe
         du_isIdempotentMonoid_910
         (coe du_'43''45'isIdempotentCommutativeMonoid_2024 (coe v1)))
-- Algebra.Structures.IsKleeneAlgebra._.isMagma
d_isMagma_2122 :: T_IsKleeneAlgebra_2044 -> T_IsMagma_176
d_isMagma_2122 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_746
            (coe
               d_'43''45'isCommutativeMonoid_1488
               (coe
                  d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0)))))))
-- Algebra.Structures.IsKleeneAlgebra._.isMonoid
d_isMonoid_2124 :: T_IsKleeneAlgebra_2044 -> T_IsMonoid_686
d_isMonoid_2124 v0
  = coe
      d_isMonoid_746
      (coe
         d_'43''45'isCommutativeMonoid_1488
         (coe
            d_isSemiringWithoutAnnihilatingZero_1584
            (coe
               d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0)))))
-- Algebra.Structures.IsKleeneAlgebra._.isSemigroup
d_isSemigroup_2126 :: T_IsKleeneAlgebra_2044 -> T_IsSemigroup_472
d_isSemigroup_2126 v0
  = coe
      d_isSemigroup_696
      (coe
         d_isMonoid_746
         (coe
            d_'43''45'isCommutativeMonoid_1488
            (coe
               d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0))))))
-- Algebra.Structures.IsKleeneAlgebra._.isUnitalMagma
d_isUnitalMagma_2128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> T_IsUnitalMagma_642
d_isUnitalMagma_2128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_2128 v9
du_isUnitalMagma_2128 ::
  T_IsKleeneAlgebra_2044 -> T_IsUnitalMagma_642
du_isUnitalMagma_2128 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe (coe du_isUnitalMagma_730 (coe d_isMonoid_746 (coe v4))))))
-- Algebra.Structures.IsKleeneAlgebra._.distrib
d_distrib_2130 ::
  T_IsKleeneAlgebra_2044 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2130 v0
  = coe
      d_distrib_1496
      (coe
         d_isSemiringWithoutAnnihilatingZero_1584
         (coe d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0))))
-- Algebra.Structures.IsKleeneAlgebra._.distribʳ
d_distrib'691'_2132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'691'_2132 v9
du_distrib'691'_2132 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2132 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (coe
            du_distrib'691'_1500
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.distribˡ
d_distrib'737'_2134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'737'_2134 v9
du_distrib'737'_2134 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2134 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (coe
            du_distrib'737'_1498
            (coe d_isSemiringWithoutAnnihilatingZero_1584 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.isEquivalence
d_isEquivalence_2136 ::
  T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2136 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_746
               (coe
                  d_'43''45'isCommutativeMonoid_1488
                  (coe
                     d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0))))))))
-- Algebra.Structures.IsKleeneAlgebra._.isNearSemiring
d_isNearSemiring_2138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2044 -> T_IsNearSemiring_1218
d_isNearSemiring_2138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isNearSemiring_2138 v9
du_isNearSemiring_2138 ::
  T_IsKleeneAlgebra_2044 -> T_IsNearSemiring_1218
du_isNearSemiring_2138 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (coe
            du_isNearSemiring_1374
            (coe du_isSemiringWithoutOne_1660 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.isPartialEquivalence
d_isPartialEquivalence_2140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_2140 v9
du_isPartialEquivalence_2140 ::
  T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2140 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (let v5 = d_isMonoid_746 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (let v7 = d_isMagma_480 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                           (coe d_isEquivalence_184 (coe v7)))))))))
-- Algebra.Structures.IsKleeneAlgebra._.isSemiring
d_isSemiring_2142 :: T_IsKleeneAlgebra_2044 -> T_IsSemiring_1570
d_isSemiring_2142 v0
  = coe d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2144 ::
  T_IsKleeneAlgebra_2044 -> T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_2144 v0
  = coe
      d_isSemiringWithoutAnnihilatingZero_1584
      (coe d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0)))
-- Algebra.Structures.IsKleeneAlgebra._.isSemiringWithoutOne
d_isSemiringWithoutOne_2146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsKleeneAlgebra_2044 -> T_IsSemiringWithoutOne_1298
d_isSemiringWithoutOne_2146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isSemiringWithoutOne_2146 v9
du_isSemiringWithoutOne_2146 ::
  T_IsKleeneAlgebra_2044 -> T_IsSemiringWithoutOne_1298
du_isSemiringWithoutOne_2146 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (coe du_isSemiringWithoutOne_1660 (coe d_isSemiring_1936 (coe v1)))
-- Algebra.Structures.IsKleeneAlgebra._.refl
d_refl_2148 :: T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
d_refl_2148 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe
                           d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0)))))))))
-- Algebra.Structures.IsKleeneAlgebra._.reflexive
d_reflexive_2150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_2150 v9
du_reflexive_2150 ::
  T_IsKleeneAlgebra_2044 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2150 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (let v5 = d_isMonoid_746 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (let v7 = d_isMagma_480 (coe v6) in
                      coe
                        (\ v8 v9 v10 ->
                           coe
                             MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                             (coe d_isEquivalence_184 (coe v7)) v8)))))))
-- Algebra.Structures.IsKleeneAlgebra._.setoid
d_setoid_2152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_2152 v9
du_setoid_2152 ::
  T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2152 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (let v3 = d_isSemiringWithoutAnnihilatingZero_1584 (coe v2) in
          coe
            (let v4 = d_'43''45'isCommutativeMonoid_1488 (coe v3) in
             coe
               (let v5 = d_isMonoid_746 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe (coe du_setoid_200 (coe d_isMagma_480 (coe v6))))))))
-- Algebra.Structures.IsKleeneAlgebra._.sym
d_sym_2154 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2154 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe
                           d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0)))))))))
-- Algebra.Structures.IsKleeneAlgebra._.trans
d_trans_2156 ::
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2156 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_746
                  (coe
                     d_'43''45'isCommutativeMonoid_1488
                     (coe
                        d_isSemiringWithoutAnnihilatingZero_1584
                        (coe
                           d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0)))))))))
-- Algebra.Structures.IsKleeneAlgebra._.zero
d_zero_2158 ::
  T_IsKleeneAlgebra_2044 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2158 v0
  = coe
      d_zero_1586
      (coe d_isSemiring_1936 (coe d_isIdempotentSemiring_2062 (coe v0)))
-- Algebra.Structures.IsKleeneAlgebra._.zeroʳ
d_zero'691'_2160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
d_zero'691'_2160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'691'_2160 v9
du_zero'691'_2160 :: T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
du_zero'691'_2160 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (coe
            du_zero'691'_1372 (coe du_isSemiringWithoutOne_1660 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra._.zeroˡ
d_zero'737'_2162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
d_zero'737'_2162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'737'_2162 v9
du_zero'737'_2162 :: T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
du_zero'737'_2162 v0
  = let v1 = d_isIdempotentSemiring_2062 (coe v0) in
    coe
      (let v2 = d_isSemiring_1936 (coe v1) in
       coe
         (coe
            du_zero'737'_1370 (coe du_isSemiringWithoutOne_1660 (coe v2))))
-- Algebra.Structures.IsKleeneAlgebra.starExpansiveˡ
d_starExpansive'737'_2164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
d_starExpansive'737'_2164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_starExpansive'737'_2164 v9
du_starExpansive'737'_2164 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
du_starExpansive'737'_2164 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_starExpansive_2064 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra.starExpansiveʳ
d_starExpansive'691'_2166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
d_starExpansive'691'_2166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_starExpansive'691'_2166 v9
du_starExpansive'691'_2166 ::
  T_IsKleeneAlgebra_2044 -> AgdaAny -> AgdaAny
du_starExpansive'691'_2166 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_starExpansive_2064 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra.starDestructiveˡ
d_starDestructive'737'_2168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_starDestructive'737'_2168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_starDestructive'737'_2168 v9
du_starDestructive'737'_2168 ::
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_starDestructive'737'_2168 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_starDestructive_2066 (coe v0))
-- Algebra.Structures.IsKleeneAlgebra.starDestructiveʳ
d_starDestructive'691'_2170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_starDestructive'691'_2170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_starDestructive'691'_2170 v9
du_starDestructive'691'_2170 ::
  T_IsKleeneAlgebra_2044 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_starDestructive'691'_2170 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_starDestructive_2066 (coe v0))
-- Algebra.Structures.IsQuasiring
d_IsQuasiring_2180 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsQuasiring_2180
  = C_IsQuasiring'46'constructor_69993 T_IsMonoid_686
                                       (AgdaAny ->
                                        AgdaAny ->
                                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsQuasiring.+-isMonoid
d_'43''45'isMonoid_2202 :: T_IsQuasiring_2180 -> T_IsMonoid_686
d_'43''45'isMonoid_2202 v0
  = case coe v0 of
      C_IsQuasiring'46'constructor_69993 v1 v2 v3 v4 v5 v6 -> coe v1
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring.*-cong
d_'42''45'cong_2204 ::
  T_IsQuasiring_2180 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2204 v0
  = case coe v0 of
      C_IsQuasiring'46'constructor_69993 v1 v2 v3 v4 v5 v6 -> coe v2
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring.*-assoc
d_'42''45'assoc_2206 ::
  T_IsQuasiring_2180 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2206 v0
  = case coe v0 of
      C_IsQuasiring'46'constructor_69993 v1 v2 v3 v4 v5 v6 -> coe v3
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring.*-identity
d_'42''45'identity_2208 ::
  T_IsQuasiring_2180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2208 v0
  = case coe v0 of
      C_IsQuasiring'46'constructor_69993 v1 v2 v3 v4 v5 v6 -> coe v4
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring.distrib
d_distrib_2210 ::
  T_IsQuasiring_2180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2210 v0
  = case coe v0 of
      C_IsQuasiring'46'constructor_69993 v1 v2 v3 v4 v5 v6 -> coe v5
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring.zero
d_zero_2212 ::
  T_IsQuasiring_2180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2212 v0
  = case coe v0 of
      C_IsQuasiring'46'constructor_69993 v1 v2 v3 v4 v5 v6 -> coe v6
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasiring._.assoc
d_assoc_2216 ::
  T_IsQuasiring_2180 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2216 v0
  = coe
      d_assoc_482
      (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_2202 (coe v0)))
-- Algebra.Structures.IsQuasiring._.∙-cong
d_'8729''45'cong_2218 ::
  T_IsQuasiring_2180 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2218 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_2202 (coe v0))))
-- Algebra.Structures.IsQuasiring._.∙-congʳ
d_'8729''45'cong'691'_2220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_2220 v8
du_'8729''45'cong'691'_2220 ::
  T_IsQuasiring_2180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2220 v0
  = let v1 = d_'43''45'isMonoid_2202 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsQuasiring._.∙-congˡ
d_'8729''45'cong'737'_2222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_2222 v8
du_'8729''45'cong'737'_2222 ::
  T_IsQuasiring_2180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2222 v0
  = let v1 = d_'43''45'isMonoid_2202 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsQuasiring._.identity
d_identity_2224 ::
  T_IsQuasiring_2180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2224 v0
  = coe d_identity_698 (coe d_'43''45'isMonoid_2202 (coe v0))
-- Algebra.Structures.IsQuasiring._.identityʳ
d_identity'691'_2226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
d_identity'691'_2226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_2226 v8
du_identity'691'_2226 :: T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
du_identity'691'_2226 v0
  = coe du_identity'691'_728 (coe d_'43''45'isMonoid_2202 (coe v0))
-- Algebra.Structures.IsQuasiring._.identityˡ
d_identity'737'_2228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
d_identity'737'_2228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_2228 v8
du_identity'737'_2228 :: T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
du_identity'737'_2228 v0
  = coe du_identity'737'_726 (coe d_'43''45'isMonoid_2202 (coe v0))
-- Algebra.Structures.IsQuasiring._.isMagma
d_isMagma_2230 :: T_IsQuasiring_2180 -> T_IsMagma_176
d_isMagma_2230 v0
  = coe
      d_isMagma_480
      (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_2202 (coe v0)))
-- Algebra.Structures.IsQuasiring._.isSemigroup
d_isSemigroup_2232 :: T_IsQuasiring_2180 -> T_IsSemigroup_472
d_isSemigroup_2232 v0
  = coe d_isSemigroup_696 (coe d_'43''45'isMonoid_2202 (coe v0))
-- Algebra.Structures.IsQuasiring._.isUnitalMagma
d_isUnitalMagma_2234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> T_IsUnitalMagma_642
d_isUnitalMagma_2234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_2234 v8
du_isUnitalMagma_2234 :: T_IsQuasiring_2180 -> T_IsUnitalMagma_642
du_isUnitalMagma_2234 v0
  = coe du_isUnitalMagma_730 (coe d_'43''45'isMonoid_2202 (coe v0))
-- Algebra.Structures.IsQuasiring._.isEquivalence
d_isEquivalence_2236 ::
  T_IsQuasiring_2180 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2236 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_2202 (coe v0))))
-- Algebra.Structures.IsQuasiring._.isPartialEquivalence
d_isPartialEquivalence_2238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2180 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2238 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_2238 v8
du_isPartialEquivalence_2238 ::
  T_IsQuasiring_2180 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2238 v0
  = let v1 = d_'43''45'isMonoid_2202 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.IsQuasiring._.refl
d_refl_2240 :: T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
d_refl_2240 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_2202 (coe v0)))))
-- Algebra.Structures.IsQuasiring._.reflexive
d_reflexive_2242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2180 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_2242 v8
du_reflexive_2242 ::
  T_IsQuasiring_2180 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2242 v0
  = let v1 = d_'43''45'isMonoid_2202 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = d_isMagma_480 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_184 (coe v3)) v4)))
-- Algebra.Structures.IsQuasiring._.setoid
d_setoid_2244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2180 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_2244 v8
du_setoid_2244 ::
  T_IsQuasiring_2180 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2244 v0
  = let v1 = d_'43''45'isMonoid_2202 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_setoid_200 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsQuasiring._.sym
d_sym_2246 ::
  T_IsQuasiring_2180 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2246 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_2202 (coe v0)))))
-- Algebra.Structures.IsQuasiring._.trans
d_trans_2248 ::
  T_IsQuasiring_2180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2248 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_2202 (coe v0)))))
-- Algebra.Structures.IsQuasiring.distribˡ
d_distrib'737'_2250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2180 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_2250 v8
du_distrib'737'_2250 ::
  T_IsQuasiring_2180 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2250 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_distrib_2210 (coe v0))
-- Algebra.Structures.IsQuasiring.distribʳ
d_distrib'691'_2252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2180 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_2252 v8
du_distrib'691'_2252 ::
  T_IsQuasiring_2180 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2252 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_distrib_2210 (coe v0))
-- Algebra.Structures.IsQuasiring.zeroˡ
d_zero'737'_2254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
d_zero'737'_2254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'737'_2254 v8
du_zero'737'_2254 :: T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
du_zero'737'_2254 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_zero_2212 (coe v0))
-- Algebra.Structures.IsQuasiring.zeroʳ
d_zero'691'_2256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
d_zero'691'_2256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_zero'691'_2256 v8
du_zero'691'_2256 :: T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
du_zero'691'_2256 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_zero_2212 (coe v0))
-- Algebra.Structures.IsQuasiring.identityˡ
d_identity'737'_2258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
d_identity'737'_2258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_2258 v8
du_identity'737'_2258 :: T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
du_identity'737'_2258 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_'42''45'identity_2208 (coe v0))
-- Algebra.Structures.IsQuasiring.identityʳ
d_identity'691'_2260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
d_identity'691'_2260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_2260 v8
du_identity'691'_2260 :: T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
du_identity'691'_2260 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_'42''45'identity_2208 (coe v0))
-- Algebra.Structures.IsQuasiring.*-isMagma
d_'42''45'isMagma_2262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> T_IsMagma_176
d_'42''45'isMagma_2262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_2262 v8
du_'42''45'isMagma_2262 :: T_IsQuasiring_2180 -> T_IsMagma_176
du_'42''45'isMagma_2262 v0
  = coe
      C_IsMagma'46'constructor_1867
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe d_isSemigroup_696 (coe d_'43''45'isMonoid_2202 (coe v0)))))
      (coe d_'42''45'cong_2204 (coe v0))
-- Algebra.Structures.IsQuasiring.*-isSemigroup
d_'42''45'isSemigroup_2264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> T_IsSemigroup_472
d_'42''45'isSemigroup_2264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_2264 v8
du_'42''45'isSemigroup_2264 ::
  T_IsQuasiring_2180 -> T_IsSemigroup_472
du_'42''45'isSemigroup_2264 v0
  = coe
      C_IsSemigroup'46'constructor_10417
      (coe du_'42''45'isMagma_2262 (coe v0))
      (coe d_'42''45'assoc_2206 (coe v0))
-- Algebra.Structures.IsQuasiring.*-isMonoid
d_'42''45'isMonoid_2266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> T_IsMonoid_686
d_'42''45'isMonoid_2266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMonoid_2266 v8
du_'42''45'isMonoid_2266 :: T_IsQuasiring_2180 -> T_IsMonoid_686
du_'42''45'isMonoid_2266 v0
  = coe
      C_IsMonoid'46'constructor_15873
      (coe du_'42''45'isSemigroup_2264 (coe v0))
      (coe d_'42''45'identity_2208 (coe v0))
-- Algebra.Structures.IsQuasiring._.∙-congʳ
d_'8729''45'cong'691'_2270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_2270 v8
du_'8729''45'cong'691'_2270 ::
  T_IsQuasiring_2180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2270 v0
  = let v1 = coe du_'42''45'isMonoid_2266 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsQuasiring._.∙-congˡ
d_'8729''45'cong'737'_2272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsQuasiring_2180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_2272 v8
du_'8729''45'cong'737'_2272 ::
  T_IsQuasiring_2180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2272 v0
  = let v1 = coe du_'42''45'isMonoid_2266 (coe v0) in
    coe
      (let v2 = d_isSemigroup_696 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsQuasiring._.identityʳ
d_identity'691'_2274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
d_identity'691'_2274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_2274 v8
du_identity'691'_2274 :: T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
du_identity'691'_2274 v0
  = coe du_identity'691'_728 (coe du_'42''45'isMonoid_2266 (coe v0))
-- Algebra.Structures.IsQuasiring._.identityˡ
d_identity'737'_2276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
d_identity'737'_2276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_2276 v8
du_identity'737'_2276 :: T_IsQuasiring_2180 -> AgdaAny -> AgdaAny
du_identity'737'_2276 v0
  = coe du_identity'737'_726 (coe du_'42''45'isMonoid_2266 (coe v0))
-- Algebra.Structures.IsRingWithoutOne
d_IsRingWithoutOne_2286 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsRingWithoutOne_2286
  = C_IsRingWithoutOne'46'constructor_75855 T_IsAbelianGroup_1132
                                            (AgdaAny ->
                                             AgdaAny ->
                                             AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                            (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                            MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsRingWithoutOne.+-isAbelianGroup
d_'43''45'isAbelianGroup_2304 ::
  T_IsRingWithoutOne_2286 -> T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_2304 v0
  = case coe v0 of
      C_IsRingWithoutOne'46'constructor_75855 v1 v2 v3 v4 -> coe v1
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRingWithoutOne.*-cong
d_'42''45'cong_2306 ::
  T_IsRingWithoutOne_2286 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2306 v0
  = case coe v0 of
      C_IsRingWithoutOne'46'constructor_75855 v1 v2 v3 v4 -> coe v2
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRingWithoutOne.*-assoc
d_'42''45'assoc_2308 ::
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2308 v0
  = case coe v0 of
      C_IsRingWithoutOne'46'constructor_75855 v1 v2 v3 v4 -> coe v3
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRingWithoutOne.distrib
d_distrib_2310 ::
  T_IsRingWithoutOne_2286 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2310 v0
  = case coe v0 of
      C_IsRingWithoutOne'46'constructor_75855 v1 v2 v3 v4 -> coe v4
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRingWithoutOne._._//_
d__'47''47'__2314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__2314 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8
  = du__'47''47'__2314 v4 v6
du__'47''47'__2314 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__2314 v0 v1 = coe du__'47''47'__1098 (coe v0) (coe v1)
-- Algebra.Structures.IsRingWithoutOne._.assoc
d_assoc_2316 ::
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2316 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_1050
            (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0)))))
-- Algebra.Structures.IsRingWithoutOne._.comm
d_comm_2318 ::
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2318 v0
  = coe d_comm_1146 (coe d_'43''45'isAbelianGroup_2304 (coe v0))
-- Algebra.Structures.IsRingWithoutOne._.∙-cong
d_'8729''45'cong_2320 ::
  T_IsRingWithoutOne_2286 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2320 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_1050
               (coe
                  d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0))))))
-- Algebra.Structures.IsRingWithoutOne._.∙-congʳ
d_'8729''45'cong'691'_2322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_2322 v8
du_'8729''45'cong'691'_2322 ::
  T_IsRingWithoutOne_2286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2322 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe
         (let v3 = d_isMonoid_1050 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsRingWithoutOne._.∙-congˡ
d_'8729''45'cong'737'_2324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_2324 v8
du_'8729''45'cong'737'_2324 ::
  T_IsRingWithoutOne_2286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2324 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe
         (let v3 = d_isMonoid_1050 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsRingWithoutOne._.identity
d_identity_2326 ::
  T_IsRingWithoutOne_2286 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2326 v0
  = coe
      d_identity_698
      (coe
         d_isMonoid_1050
         (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0))))
-- Algebra.Structures.IsRingWithoutOne._.identityʳ
d_identity'691'_2328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
d_identity'691'_2328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_2328 v8
du_identity'691'_2328 ::
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
du_identity'691'_2328 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe (coe du_identity'691'_728 (coe d_isMonoid_1050 (coe v2))))
-- Algebra.Structures.IsRingWithoutOne._.identityˡ
d_identity'737'_2330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
d_identity'737'_2330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_2330 v8
du_identity'737'_2330 ::
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
du_identity'737'_2330 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe (coe du_identity'737'_726 (coe d_isMonoid_1050 (coe v2))))
-- Algebra.Structures.IsRingWithoutOne._.isCommutativeMagma
d_isCommutativeMagma_2332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_2332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMagma_2332 v8
du_isCommutativeMagma_2332 ::
  T_IsRingWithoutOne_2286 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_2332 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe
      (let v2 = coe du_isCommutativeMonoid_1204 (coe v1) in
       coe
         (coe
            du_isCommutativeMagma_586
            (coe du_isCommutativeSemigroup_786 (coe v2))))
-- Algebra.Structures.IsRingWithoutOne._.isCommutativeMonoid
d_isCommutativeMonoid_2334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> T_IsCommutativeMonoid_736
d_isCommutativeMonoid_2334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeMonoid_2334 v8
du_isCommutativeMonoid_2334 ::
  T_IsRingWithoutOne_2286 -> T_IsCommutativeMonoid_736
du_isCommutativeMonoid_2334 v0
  = coe
      du_isCommutativeMonoid_1204
      (coe d_'43''45'isAbelianGroup_2304 (coe v0))
-- Algebra.Structures.IsRingWithoutOne._.isCommutativeSemigroup
d_isCommutativeSemigroup_2336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_2336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isCommutativeSemigroup_2336 v8
du_isCommutativeSemigroup_2336 ::
  T_IsRingWithoutOne_2286 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_2336 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe
      (coe
         du_isCommutativeSemigroup_786
         (coe du_isCommutativeMonoid_1204 (coe v1)))
-- Algebra.Structures.IsRingWithoutOne._.isGroup
d_isGroup_2338 :: T_IsRingWithoutOne_2286 -> T_IsGroup_1036
d_isGroup_2338 v0
  = coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0))
-- Algebra.Structures.IsRingWithoutOne._.isInvertibleMagma
d_isInvertibleMagma_2340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> T_IsInvertibleMagma_924
d_isInvertibleMagma_2340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isInvertibleMagma_2340 v8
du_isInvertibleMagma_2340 ::
  T_IsRingWithoutOne_2286 -> T_IsInvertibleMagma_924
du_isInvertibleMagma_2340 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe (coe du_isInvertibleMagma_1122 (coe d_isGroup_1144 (coe v1)))
-- Algebra.Structures.IsRingWithoutOne._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> T_IsInvertibleUnitalMagma_976
d_isInvertibleUnitalMagma_2342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isInvertibleUnitalMagma_2342 v8
du_isInvertibleUnitalMagma_2342 ::
  T_IsRingWithoutOne_2286 -> T_IsInvertibleUnitalMagma_976
du_isInvertibleUnitalMagma_2342 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe
      (coe du_isInvertibleUnitalMagma_1124 (coe d_isGroup_1144 (coe v1)))
-- Algebra.Structures.IsRingWithoutOne._.isMagma
d_isMagma_2344 :: T_IsRingWithoutOne_2286 -> T_IsMagma_176
d_isMagma_2344 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_1050
            (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0)))))
-- Algebra.Structures.IsRingWithoutOne._.isMonoid
d_isMonoid_2346 :: T_IsRingWithoutOne_2286 -> T_IsMonoid_686
d_isMonoid_2346 v0
  = coe
      d_isMonoid_1050
      (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0)))
-- Algebra.Structures.IsRingWithoutOne._.isSemigroup
d_isSemigroup_2348 :: T_IsRingWithoutOne_2286 -> T_IsSemigroup_472
d_isSemigroup_2348 v0
  = coe
      d_isSemigroup_696
      (coe
         d_isMonoid_1050
         (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0))))
-- Algebra.Structures.IsRingWithoutOne._.isUnitalMagma
d_isUnitalMagma_2350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> T_IsUnitalMagma_642
d_isUnitalMagma_2350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_2350 v8
du_isUnitalMagma_2350 ::
  T_IsRingWithoutOne_2286 -> T_IsUnitalMagma_642
du_isUnitalMagma_2350 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe (coe du_isUnitalMagma_730 (coe d_isMonoid_1050 (coe v2))))
-- Algebra.Structures.IsRingWithoutOne._.⁻¹-cong
d_'8315''185''45'cong_2352 ::
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_2352 v0
  = coe
      d_'8315''185''45'cong_1054
      (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0)))
-- Algebra.Structures.IsRingWithoutOne._.inverse
d_inverse_2354 ::
  T_IsRingWithoutOne_2286 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2354 v0
  = coe
      d_inverse_1052
      (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0)))
-- Algebra.Structures.IsRingWithoutOne._.inverseʳ
d_inverse'691'_2356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
d_inverse'691'_2356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_inverse'691'_2356 v8
du_inverse'691'_2356 ::
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
du_inverse'691'_2356 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe (coe du_inverse'691'_1108 (coe d_isGroup_1144 (coe v1)))
-- Algebra.Structures.IsRingWithoutOne._.inverseˡ
d_inverse'737'_2358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
d_inverse'737'_2358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_inverse'737'_2358 v8
du_inverse'737'_2358 ::
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
du_inverse'737'_2358 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe (coe du_inverse'737'_1106 (coe d_isGroup_1144 (coe v1)))
-- Algebra.Structures.IsRingWithoutOne._.isEquivalence
d_isEquivalence_2360 ::
  T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2360 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_1050
               (coe
                  d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0))))))
-- Algebra.Structures.IsRingWithoutOne._.isPartialEquivalence
d_isPartialEquivalence_2362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2362 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_2362 v8
du_isPartialEquivalence_2362 ::
  T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2362 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe
         (let v3 = d_isMonoid_1050 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (let v5 = d_isMagma_480 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                     (coe d_isEquivalence_184 (coe v5)))))))
-- Algebra.Structures.IsRingWithoutOne._.refl
d_refl_2364 :: T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
d_refl_2364 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0)))))))
-- Algebra.Structures.IsRingWithoutOne._.reflexive
d_reflexive_2366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_2366 v8
du_reflexive_2366 ::
  T_IsRingWithoutOne_2286 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2366 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe
         (let v3 = d_isMonoid_1050 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (let v5 = d_isMagma_480 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                       (coe d_isEquivalence_184 (coe v5)) v6)))))
-- Algebra.Structures.IsRingWithoutOne._.setoid
d_setoid_2368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_2368 v8
du_setoid_2368 ::
  T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2368 v0
  = let v1 = d_'43''45'isAbelianGroup_2304 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe
         (let v3 = d_isMonoid_1050 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe (coe du_setoid_200 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsRingWithoutOne._.sym
d_sym_2370 ::
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2370 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0)))))))
-- Algebra.Structures.IsRingWithoutOne._.trans
d_trans_2372 ::
  T_IsRingWithoutOne_2286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2372 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0)))))))
-- Algebra.Structures.IsRingWithoutOne._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_2374 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8
  = du_unique'691''45''8315''185'_2374 v4 v6 v7 v8
du_unique'691''45''8315''185'_2374 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_2374 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_2304 (coe v3) in
    coe
      (coe
         du_unique'691''45''8315''185'_1120 (coe v0) (coe v2) (coe v1)
         (coe d_isGroup_1144 (coe v4)))
-- Algebra.Structures.IsRingWithoutOne._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_2376 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8
  = du_unique'737''45''8315''185'_2376 v4 v6 v7 v8
du_unique'737''45''8315''185'_2376 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_2376 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_2304 (coe v3) in
    coe
      (coe
         du_unique'737''45''8315''185'_1114 (coe v0) (coe v2) (coe v1)
         (coe d_isGroup_1144 (coe v4)))
-- Algebra.Structures.IsRingWithoutOne.distribˡ
d_distrib'737'_2378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2378 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'737'_2378 v8
du_distrib'737'_2378 ::
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2378 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_distrib_2310 (coe v0))
-- Algebra.Structures.IsRingWithoutOne.distribʳ
d_distrib'691'_2380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_distrib'691'_2380 v8
du_distrib'691'_2380 ::
  T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2380 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_distrib_2310 (coe v0))
-- Algebra.Structures.IsRingWithoutOne.zeroˡ
d_zero'737'_2382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
d_zero'737'_2382 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_zero'737'_2382 v4 v5 v6 v7 v8
du_zero'737'_2382 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
du_zero'737'_2382 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'distrib'691''8743'id'691''8743'inv'691''8658'ze'737'_594
      (let v5
             = d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v4)) in
       coe
         (let v6 = d_isMonoid_1050 (coe v5) in
          coe
            (let v7 = d_isSemigroup_696 (coe v6) in
             coe (coe du_setoid_200 (coe d_isMagma_480 (coe v7))))))
      (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         d_'8729''45'cong_186
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v4)))))))
      (coe d_'42''45'cong_2306 (coe v4))
      (coe
         d_assoc_482
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_1050
               (coe
                  d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v4))))))
      (coe du_distrib'691'_2380 (coe v4))
      (let v5
             = d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v4)) in
       coe (coe du_identity'691'_728 (coe d_isMonoid_1050 (coe v5))))
      (coe
         du_inverse'691'_1108
         (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v4))))
-- Algebra.Structures.IsRingWithoutOne.zeroʳ
d_zero'691'_2384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
d_zero'691'_2384 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_zero'691'_2384 v4 v5 v6 v7 v8
du_zero'691'_2384 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> AgdaAny -> AgdaAny
du_zero'691'_2384 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'distrib'737''8743'id'691''8743'inv'691''8658'ze'691'_606
      (let v5
             = d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v4)) in
       coe
         (let v6 = d_isMonoid_1050 (coe v5) in
          coe
            (let v7 = d_isSemigroup_696 (coe v6) in
             coe (coe du_setoid_200 (coe d_isMagma_480 (coe v7))))))
      (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         d_'8729''45'cong_186
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v4)))))))
      (coe d_'42''45'cong_2306 (coe v4))
      (coe
         d_assoc_482
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_1050
               (coe
                  d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v4))))))
      (coe du_distrib'737'_2378 (coe v4))
      (let v5
             = d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v4)) in
       coe (coe du_identity'691'_728 (coe d_isMonoid_1050 (coe v5))))
      (coe
         du_inverse'691'_1108
         (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v4))))
-- Algebra.Structures.IsRingWithoutOne.zero
d_zero_2386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2386 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_zero_2386 v4 v5 v6 v7 v8
du_zero_2386 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_2386 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_zero'737'_2382 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      (coe
         du_zero'691'_2384 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Structures.IsRingWithoutOne.*-isMagma
d_'42''45'isMagma_2388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> T_IsMagma_176
d_'42''45'isMagma_2388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isMagma_2388 v8
du_'42''45'isMagma_2388 :: T_IsRingWithoutOne_2286 -> T_IsMagma_176
du_'42''45'isMagma_2388 v0
  = coe
      C_IsMagma'46'constructor_1867
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2304 (coe v0)))))))
      (coe d_'42''45'cong_2306 (coe v0))
-- Algebra.Structures.IsRingWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_2390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRingWithoutOne_2286 -> T_IsSemigroup_472
d_'42''45'isSemigroup_2390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'42''45'isSemigroup_2390 v8
du_'42''45'isSemigroup_2390 ::
  T_IsRingWithoutOne_2286 -> T_IsSemigroup_472
du_'42''45'isSemigroup_2390 v0
  = coe
      C_IsSemigroup'46'constructor_10417
      (coe du_'42''45'isMagma_2388 (coe v0))
      (coe d_'42''45'assoc_2308 (coe v0))
-- Algebra.Structures.IsRingWithoutOne._.∙-congʳ
d_'8729''45'cong'691'_2394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_2394 v8
du_'8729''45'cong'691'_2394 ::
  T_IsRingWithoutOne_2286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2394 v0
  = let v1 = coe du_'42''45'isSemigroup_2390 (coe v0) in
    coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v1)))
-- Algebra.Structures.IsRingWithoutOne._.∙-congˡ
d_'8729''45'cong'737'_2396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutOne_2286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_2396 v8
du_'8729''45'cong'737'_2396 ::
  T_IsRingWithoutOne_2286 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2396 v0
  = let v1 = coe du_'42''45'isSemigroup_2390 (coe v0) in
    coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing
d_IsNonAssociativeRing_2408 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsNonAssociativeRing_2408
  = C_IsNonAssociativeRing'46'constructor_83447 T_IsAbelianGroup_1132
                                                (AgdaAny ->
                                                 AgdaAny ->
                                                 AgdaAny ->
                                                 AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                                MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                                MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                                MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsNonAssociativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2430 ::
  T_IsNonAssociativeRing_2408 -> T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_2430 v0
  = case coe v0 of
      C_IsNonAssociativeRing'46'constructor_83447 v1 v2 v3 v4 v5
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNonAssociativeRing.*-cong
d_'42''45'cong_2432 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2432 v0
  = case coe v0 of
      C_IsNonAssociativeRing'46'constructor_83447 v1 v2 v3 v4 v5
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNonAssociativeRing.*-identity
d_'42''45'identity_2434 ::
  T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2434 v0
  = case coe v0 of
      C_IsNonAssociativeRing'46'constructor_83447 v1 v2 v3 v4 v5
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNonAssociativeRing.distrib
d_distrib_2436 ::
  T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2436 v0
  = case coe v0 of
      C_IsNonAssociativeRing'46'constructor_83447 v1 v2 v3 v4 v5
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNonAssociativeRing.zero
d_zero_2438 ::
  T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2438 v0
  = case coe v0 of
      C_IsNonAssociativeRing'46'constructor_83447 v1 v2 v3 v4 v5
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNonAssociativeRing._._//_
d__'47''47'__2442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__2442 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du__'47''47'__2442 v4 v6
du__'47''47'__2442 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__2442 v0 v1 = coe du__'47''47'__1098 (coe v0) (coe v1)
-- Algebra.Structures.IsNonAssociativeRing._.assoc
d_assoc_2444 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2444 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_1050
            (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0)))))
-- Algebra.Structures.IsNonAssociativeRing._.comm
d_comm_2446 ::
  T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2446 v0
  = coe d_comm_1146 (coe d_'43''45'isAbelianGroup_2430 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing._.∙-cong
d_'8729''45'cong_2448 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2448 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_1050
               (coe
                  d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0))))))
-- Algebra.Structures.IsNonAssociativeRing._.∙-congʳ
d_'8729''45'cong'691'_2450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2450 v9
du_'8729''45'cong'691'_2450 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2450 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe
         (let v3 = d_isMonoid_1050 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsNonAssociativeRing._.∙-congˡ
d_'8729''45'cong'737'_2452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2452 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2452 v9
du_'8729''45'cong'737'_2452 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2452 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe
         (let v3 = d_isMonoid_1050 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsNonAssociativeRing._.identity
d_identity_2454 ::
  T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2454 v0
  = coe
      d_identity_698
      (coe
         d_isMonoid_1050
         (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0))))
-- Algebra.Structures.IsNonAssociativeRing._.identityʳ
d_identity'691'_2456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
d_identity'691'_2456 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2456 v9
du_identity'691'_2456 ::
  T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
du_identity'691'_2456 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe (coe du_identity'691'_728 (coe d_isMonoid_1050 (coe v2))))
-- Algebra.Structures.IsNonAssociativeRing._.identityˡ
d_identity'737'_2458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
d_identity'737'_2458 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2458 v9
du_identity'737'_2458 ::
  T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
du_identity'737'_2458 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe (coe du_identity'737'_726 (coe d_isMonoid_1050 (coe v2))))
-- Algebra.Structures.IsNonAssociativeRing._.isCommutativeMagma
d_isCommutativeMagma_2460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_2460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_2460 v9
du_isCommutativeMagma_2460 ::
  T_IsNonAssociativeRing_2408 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_2460 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe
      (let v2 = coe du_isCommutativeMonoid_1204 (coe v1) in
       coe
         (coe
            du_isCommutativeMagma_586
            (coe du_isCommutativeSemigroup_786 (coe v2))))
-- Algebra.Structures.IsNonAssociativeRing._.isCommutativeMonoid
d_isCommutativeMonoid_2462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> T_IsCommutativeMonoid_736
d_isCommutativeMonoid_2462 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMonoid_2462 v9
du_isCommutativeMonoid_2462 ::
  T_IsNonAssociativeRing_2408 -> T_IsCommutativeMonoid_736
du_isCommutativeMonoid_2462 v0
  = coe
      du_isCommutativeMonoid_1204
      (coe d_'43''45'isAbelianGroup_2430 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing._.isCommutativeSemigroup
d_isCommutativeSemigroup_2464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_2464 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              v9
  = du_isCommutativeSemigroup_2464 v9
du_isCommutativeSemigroup_2464 ::
  T_IsNonAssociativeRing_2408 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_2464 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe
      (coe
         du_isCommutativeSemigroup_786
         (coe du_isCommutativeMonoid_1204 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing._.isGroup
d_isGroup_2466 :: T_IsNonAssociativeRing_2408 -> T_IsGroup_1036
d_isGroup_2466 v0
  = coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing._.isInvertibleMagma
d_isInvertibleMagma_2468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> T_IsInvertibleMagma_924
d_isInvertibleMagma_2468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isInvertibleMagma_2468 v9
du_isInvertibleMagma_2468 ::
  T_IsNonAssociativeRing_2408 -> T_IsInvertibleMagma_924
du_isInvertibleMagma_2468 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe (coe du_isInvertibleMagma_1122 (coe d_isGroup_1144 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 -> T_IsInvertibleUnitalMagma_976
d_isInvertibleUnitalMagma_2470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_isInvertibleUnitalMagma_2470 v9
du_isInvertibleUnitalMagma_2470 ::
  T_IsNonAssociativeRing_2408 -> T_IsInvertibleUnitalMagma_976
du_isInvertibleUnitalMagma_2470 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe
      (coe du_isInvertibleUnitalMagma_1124 (coe d_isGroup_1144 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing._.isMagma
d_isMagma_2472 :: T_IsNonAssociativeRing_2408 -> T_IsMagma_176
d_isMagma_2472 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_1050
            (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0)))))
-- Algebra.Structures.IsNonAssociativeRing._.isMonoid
d_isMonoid_2474 :: T_IsNonAssociativeRing_2408 -> T_IsMonoid_686
d_isMonoid_2474 v0
  = coe
      d_isMonoid_1050
      (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0)))
-- Algebra.Structures.IsNonAssociativeRing._.isSemigroup
d_isSemigroup_2476 ::
  T_IsNonAssociativeRing_2408 -> T_IsSemigroup_472
d_isSemigroup_2476 v0
  = coe
      d_isSemigroup_696
      (coe
         d_isMonoid_1050
         (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0))))
-- Algebra.Structures.IsNonAssociativeRing._.isUnitalMagma
d_isUnitalMagma_2478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> T_IsUnitalMagma_642
d_isUnitalMagma_2478 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_2478 v9
du_isUnitalMagma_2478 ::
  T_IsNonAssociativeRing_2408 -> T_IsUnitalMagma_642
du_isUnitalMagma_2478 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe (coe du_isUnitalMagma_730 (coe d_isMonoid_1050 (coe v2))))
-- Algebra.Structures.IsNonAssociativeRing._.⁻¹-cong
d_'8315''185''45'cong_2480 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_2480 v0
  = coe
      d_'8315''185''45'cong_1054
      (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0)))
-- Algebra.Structures.IsNonAssociativeRing._.inverse
d_inverse_2482 ::
  T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2482 v0
  = coe
      d_inverse_1052
      (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0)))
-- Algebra.Structures.IsNonAssociativeRing._.inverseʳ
d_inverse'691'_2484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
d_inverse'691'_2484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'691'_2484 v9
du_inverse'691'_2484 ::
  T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
du_inverse'691'_2484 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe (coe du_inverse'691'_1108 (coe d_isGroup_1144 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing._.inverseˡ
d_inverse'737'_2486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
d_inverse'737'_2486 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'737'_2486 v9
du_inverse'737'_2486 ::
  T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
du_inverse'737'_2486 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe (coe du_inverse'737'_1106 (coe d_isGroup_1144 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing._.isEquivalence
d_isEquivalence_2488 ::
  T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2488 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_1050
               (coe
                  d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0))))))
-- Algebra.Structures.IsNonAssociativeRing._.isPartialEquivalence
d_isPartialEquivalence_2490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_2490 v9
du_isPartialEquivalence_2490 ::
  T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2490 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe
         (let v3 = d_isMonoid_1050 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (let v5 = d_isMagma_480 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                     (coe d_isEquivalence_184 (coe v5)))))))
-- Algebra.Structures.IsNonAssociativeRing._.refl
d_refl_2492 :: T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
d_refl_2492 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0)))))))
-- Algebra.Structures.IsNonAssociativeRing._.reflexive
d_reflexive_2494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_2494 v9
du_reflexive_2494 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2494 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe
         (let v3 = d_isMonoid_1050 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe
               (let v5 = d_isMagma_480 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                       (coe d_isEquivalence_184 (coe v5)) v6)))))
-- Algebra.Structures.IsNonAssociativeRing._.setoid
d_setoid_2496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_2496 v9
du_setoid_2496 ::
  T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2496 v0
  = let v1 = d_'43''45'isAbelianGroup_2430 (coe v0) in
    coe
      (let v2 = d_isGroup_1144 (coe v1) in
       coe
         (let v3 = d_isMonoid_1050 (coe v2) in
          coe
            (let v4 = d_isSemigroup_696 (coe v3) in
             coe (coe du_setoid_200 (coe d_isMagma_480 (coe v4))))))
-- Algebra.Structures.IsNonAssociativeRing._.sym
d_sym_2498 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2498 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0)))))))
-- Algebra.Structures.IsNonAssociativeRing._.trans
d_trans_2500 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2500 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0)))))))
-- Algebra.Structures.IsNonAssociativeRing._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_2502 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'691''45''8315''185'_2502 v4 v6 v7 v9
du_unique'691''45''8315''185'_2502 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_2502 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_2430 (coe v3) in
    coe
      (coe
         du_unique'691''45''8315''185'_1120 (coe v0) (coe v2) (coe v1)
         (coe d_isGroup_1144 (coe v4)))
-- Algebra.Structures.IsNonAssociativeRing._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_2504 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'737''45''8315''185'_2504 v4 v6 v7 v9
du_unique'737''45''8315''185'_2504 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_2504 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_2430 (coe v3) in
    coe
      (coe
         du_unique'737''45''8315''185'_1114 (coe v0) (coe v2) (coe v1)
         (coe d_isGroup_1144 (coe v4)))
-- Algebra.Structures.IsNonAssociativeRing.zeroˡ
d_zero'737'_2506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
d_zero'737'_2506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'737'_2506 v9
du_zero'737'_2506 ::
  T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
du_zero'737'_2506 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_zero_2438 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.zeroʳ
d_zero'691'_2508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
d_zero'691'_2508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'691'_2508 v9
du_zero'691'_2508 ::
  T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
du_zero'691'_2508 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_zero_2438 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.distribˡ
d_distrib'737'_2510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'737'_2510 v9
du_distrib'737'_2510 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2510 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_distrib_2436 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.distribʳ
d_distrib'691'_2512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'691'_2512 v9
du_distrib'691'_2512 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2512 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_distrib_2436 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.*-isMagma
d_'42''45'isMagma_2514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsNonAssociativeRing_2408 -> T_IsMagma_176
d_'42''45'isMagma_2514 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMagma_2514 v9
du_'42''45'isMagma_2514 ::
  T_IsNonAssociativeRing_2408 -> T_IsMagma_176
du_'42''45'isMagma_2514 v0
  = coe
      C_IsMagma'46'constructor_1867
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2430 (coe v0)))))))
      (coe d_'42''45'cong_2432 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.*-identityˡ
d_'42''45'identity'737'_2516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
d_'42''45'identity'737'_2516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'identity'737'_2516 v9
du_'42''45'identity'737'_2516 ::
  T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
du_'42''45'identity'737'_2516 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_'42''45'identity_2434 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.*-identityʳ
d_'42''45'identity'691'_2518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
d_'42''45'identity'691'_2518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'identity'691'_2518 v9
du_'42''45'identity'691'_2518 ::
  T_IsNonAssociativeRing_2408 -> AgdaAny -> AgdaAny
du_'42''45'identity'691'_2518 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_'42''45'identity_2434 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing.*-isUnitalMagma
d_'42''45'isUnitalMagma_2520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsNonAssociativeRing_2408 -> T_IsUnitalMagma_642
d_'42''45'isUnitalMagma_2520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isUnitalMagma_2520 v9
du_'42''45'isUnitalMagma_2520 ::
  T_IsNonAssociativeRing_2408 -> T_IsUnitalMagma_642
du_'42''45'isUnitalMagma_2520 v0
  = coe
      C_IsUnitalMagma'46'constructor_14317
      (coe du_'42''45'isMagma_2514 (coe v0))
      (coe d_'42''45'identity_2434 (coe v0))
-- Algebra.Structures.IsNonAssociativeRing._.∙-congʳ
d_'8729''45'cong'691'_2524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2524 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2524 v9
du_'8729''45'cong'691'_2524 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2524 v0
  = let v1 = coe du_'42''45'isUnitalMagma_2520 (coe v0) in
    coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_652 (coe v1)))
-- Algebra.Structures.IsNonAssociativeRing._.∙-congˡ
d_'8729''45'cong'737'_2526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2526 v9
du_'8729''45'cong'737'_2526 ::
  T_IsNonAssociativeRing_2408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2526 v0
  = let v1 = coe du_'42''45'isUnitalMagma_2520 (coe v0) in
    coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_652 (coe v1)))
-- Algebra.Structures.IsNearring
d_IsNearring_2538 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsNearring_2538
  = C_IsNearring'46'constructor_90609 T_IsQuasiring_2180
                                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsNearring.isQuasiring
d_isQuasiring_2556 :: T_IsNearring_2538 -> T_IsQuasiring_2180
d_isQuasiring_2556 v0
  = case coe v0 of
      C_IsNearring'46'constructor_90609 v1 v2 v3 -> coe v1
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearring.+-inverse
d_'43''45'inverse_2558 ::
  T_IsNearring_2538 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_2558 v0
  = case coe v0 of
      C_IsNearring'46'constructor_90609 v1 v2 v3 -> coe v2
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearring.⁻¹-cong
d_'8315''185''45'cong_2560 ::
  T_IsNearring_2538 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_2560 v0
  = case coe v0 of
      C_IsNearring'46'constructor_90609 v1 v2 v3 -> coe v3
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsNearring._.*-assoc
d_'42''45'assoc_2564 ::
  T_IsNearring_2538 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2564 v0
  = coe d_'42''45'assoc_2206 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.*-cong
d_'42''45'cong_2566 ::
  T_IsNearring_2538 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2566 v0
  = coe d_'42''45'cong_2204 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.∙-congʳ
d_'8729''45'cong'691'_2568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2538 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2568 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2568 v9
du_'8729''45'cong'691'_2568 ::
  T_IsNearring_2538 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2568 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isMonoid_2266 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsNearring._.∙-congˡ
d_'8729''45'cong'737'_2570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2538 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2570 v9
du_'8729''45'cong'737'_2570 ::
  T_IsNearring_2538 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2570 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isMonoid_2266 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsNearring._.*-identity
d_'42''45'identity_2572 ::
  T_IsNearring_2538 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2572 v0
  = coe d_'42''45'identity_2208 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.identityʳ
d_identity'691'_2574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> AgdaAny -> AgdaAny
d_identity'691'_2574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2574 v9
du_identity'691'_2574 :: T_IsNearring_2538 -> AgdaAny -> AgdaAny
du_identity'691'_2574 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (coe du_identity'691'_728 (coe du_'42''45'isMonoid_2266 (coe v1)))
-- Algebra.Structures.IsNearring._.identityˡ
d_identity'737'_2576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> AgdaAny -> AgdaAny
d_identity'737'_2576 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2576 v9
du_identity'737'_2576 :: T_IsNearring_2538 -> AgdaAny -> AgdaAny
du_identity'737'_2576 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (coe du_identity'737'_726 (coe du_'42''45'isMonoid_2266 (coe v1)))
-- Algebra.Structures.IsNearring._.*-isMagma
d_'42''45'isMagma_2578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> T_IsMagma_176
d_'42''45'isMagma_2578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMagma_2578 v9
du_'42''45'isMagma_2578 :: T_IsNearring_2538 -> T_IsMagma_176
du_'42''45'isMagma_2578 v0
  = coe du_'42''45'isMagma_2262 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.*-isMonoid
d_'42''45'isMonoid_2580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> T_IsMonoid_686
d_'42''45'isMonoid_2580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMonoid_2580 v9
du_'42''45'isMonoid_2580 :: T_IsNearring_2538 -> T_IsMonoid_686
du_'42''45'isMonoid_2580 v0
  = coe du_'42''45'isMonoid_2266 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.*-isSemigroup
d_'42''45'isSemigroup_2582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> T_IsSemigroup_472
d_'42''45'isSemigroup_2582 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isSemigroup_2582 v9
du_'42''45'isSemigroup_2582 ::
  T_IsNearring_2538 -> T_IsSemigroup_472
du_'42''45'isSemigroup_2582 v0
  = coe du_'42''45'isSemigroup_2264 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.assoc
d_assoc_2584 ::
  T_IsNearring_2538 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2584 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe d_'43''45'isMonoid_2202 (coe d_isQuasiring_2556 (coe v0))))
-- Algebra.Structures.IsNearring._.∙-cong
d_'8729''45'cong_2586 ::
  T_IsNearring_2538 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2586 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe d_'43''45'isMonoid_2202 (coe d_isQuasiring_2556 (coe v0)))))
-- Algebra.Structures.IsNearring._.∙-congʳ
d_'8729''45'cong'691'_2588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2538 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2588 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2588 v9
du_'8729''45'cong'691'_2588 ::
  T_IsNearring_2538 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2588 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (let v2 = d_'43''45'isMonoid_2202 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsNearring._.∙-congˡ
d_'8729''45'cong'737'_2590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2538 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2590 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2590 v9
du_'8729''45'cong'737'_2590 ::
  T_IsNearring_2538 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2590 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (let v2 = d_'43''45'isMonoid_2202 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsNearring._.identity
d_identity_2592 ::
  T_IsNearring_2538 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2592 v0
  = coe
      d_identity_698
      (coe d_'43''45'isMonoid_2202 (coe d_isQuasiring_2556 (coe v0)))
-- Algebra.Structures.IsNearring._.identityʳ
d_identity'691'_2594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> AgdaAny -> AgdaAny
d_identity'691'_2594 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2594 v9
du_identity'691'_2594 :: T_IsNearring_2538 -> AgdaAny -> AgdaAny
du_identity'691'_2594 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (coe du_identity'691'_728 (coe d_'43''45'isMonoid_2202 (coe v1)))
-- Algebra.Structures.IsNearring._.identityˡ
d_identity'737'_2596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> AgdaAny -> AgdaAny
d_identity'737'_2596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2596 v9
du_identity'737'_2596 :: T_IsNearring_2538 -> AgdaAny -> AgdaAny
du_identity'737'_2596 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (coe du_identity'737'_726 (coe d_'43''45'isMonoid_2202 (coe v1)))
-- Algebra.Structures.IsNearring._.isMagma
d_isMagma_2598 :: T_IsNearring_2538 -> T_IsMagma_176
d_isMagma_2598 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe d_'43''45'isMonoid_2202 (coe d_isQuasiring_2556 (coe v0))))
-- Algebra.Structures.IsNearring._.+-isMonoid
d_'43''45'isMonoid_2600 :: T_IsNearring_2538 -> T_IsMonoid_686
d_'43''45'isMonoid_2600 v0
  = coe d_'43''45'isMonoid_2202 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.isSemigroup
d_isSemigroup_2602 :: T_IsNearring_2538 -> T_IsSemigroup_472
d_isSemigroup_2602 v0
  = coe
      d_isSemigroup_696
      (coe d_'43''45'isMonoid_2202 (coe d_isQuasiring_2556 (coe v0)))
-- Algebra.Structures.IsNearring._.isUnitalMagma
d_isUnitalMagma_2604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> T_IsUnitalMagma_642
d_isUnitalMagma_2604 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_2604 v9
du_isUnitalMagma_2604 :: T_IsNearring_2538 -> T_IsUnitalMagma_642
du_isUnitalMagma_2604 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (coe du_isUnitalMagma_730 (coe d_'43''45'isMonoid_2202 (coe v1)))
-- Algebra.Structures.IsNearring._.distrib
d_distrib_2606 ::
  T_IsNearring_2538 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2606 v0
  = coe d_distrib_2210 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.distribʳ
d_distrib'691'_2608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2538 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'691'_2608 v9
du_distrib'691'_2608 ::
  T_IsNearring_2538 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2608 v0
  = coe du_distrib'691'_2252 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.distribˡ
d_distrib'737'_2610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2538 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'737'_2610 v9
du_distrib'737'_2610 ::
  T_IsNearring_2538 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2610 v0
  = coe du_distrib'737'_2250 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.identityʳ
d_identity'691'_2612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> AgdaAny -> AgdaAny
d_identity'691'_2612 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2612 v9
du_identity'691'_2612 :: T_IsNearring_2538 -> AgdaAny -> AgdaAny
du_identity'691'_2612 v0
  = coe du_identity'691'_2260 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.identityˡ
d_identity'737'_2614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> AgdaAny -> AgdaAny
d_identity'737'_2614 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2614 v9
du_identity'737'_2614 :: T_IsNearring_2538 -> AgdaAny -> AgdaAny
du_identity'737'_2614 v0
  = coe du_identity'737'_2258 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.isEquivalence
d_isEquivalence_2616 ::
  T_IsNearring_2538 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2616 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe d_'43''45'isMonoid_2202 (coe d_isQuasiring_2556 (coe v0)))))
-- Algebra.Structures.IsNearring._.isPartialEquivalence
d_isPartialEquivalence_2618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2538 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2618 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_2618 v9
du_isPartialEquivalence_2618 ::
  T_IsNearring_2538 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2618 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (let v2 = d_'43''45'isMonoid_2202 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe
            (let v4 = d_isMagma_480 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe d_isEquivalence_184 (coe v4))))))
-- Algebra.Structures.IsNearring._.refl
d_refl_2620 :: T_IsNearring_2538 -> AgdaAny -> AgdaAny
d_refl_2620 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe d_'43''45'isMonoid_2202 (coe d_isQuasiring_2556 (coe v0))))))
-- Algebra.Structures.IsNearring._.reflexive
d_reflexive_2622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2538 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2622 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_2622 v9
du_reflexive_2622 ::
  T_IsNearring_2538 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2622 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (let v2 = d_'43''45'isMonoid_2202 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe
            (let v4 = d_isMagma_480 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe d_isEquivalence_184 (coe v4)) v5))))
-- Algebra.Structures.IsNearring._.setoid
d_setoid_2624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  T_IsNearring_2538 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_2624 v9
du_setoid_2624 ::
  T_IsNearring_2538 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2624 v0
  = let v1 = d_isQuasiring_2556 (coe v0) in
    coe
      (let v2 = d_'43''45'isMonoid_2202 (coe v1) in
       coe
         (let v3 = d_isSemigroup_696 (coe v2) in
          coe (coe du_setoid_200 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsNearring._.sym
d_sym_2626 ::
  T_IsNearring_2538 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2626 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe d_'43''45'isMonoid_2202 (coe d_isQuasiring_2556 (coe v0))))))
-- Algebra.Structures.IsNearring._.trans
d_trans_2628 ::
  T_IsNearring_2538 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2628 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe d_'43''45'isMonoid_2202 (coe d_isQuasiring_2556 (coe v0))))))
-- Algebra.Structures.IsNearring._.zero
d_zero_2630 ::
  T_IsNearring_2538 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2630 v0 = coe d_zero_2212 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.zeroʳ
d_zero'691'_2632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> AgdaAny -> AgdaAny
d_zero'691'_2632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'691'_2632 v9
du_zero'691'_2632 :: T_IsNearring_2538 -> AgdaAny -> AgdaAny
du_zero'691'_2632 v0
  = coe du_zero'691'_2256 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring._.zeroˡ
d_zero'737'_2634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> AgdaAny -> AgdaAny
d_zero'737'_2634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_zero'737'_2634 v9
du_zero'737'_2634 :: T_IsNearring_2538 -> AgdaAny -> AgdaAny
du_zero'737'_2634 v0
  = coe du_zero'737'_2254 (coe d_isQuasiring_2556 (coe v0))
-- Algebra.Structures.IsNearring.+-inverseˡ
d_'43''45'inverse'737'_2636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> AgdaAny -> AgdaAny
d_'43''45'inverse'737'_2636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'43''45'inverse'737'_2636 v9
du_'43''45'inverse'737'_2636 ::
  T_IsNearring_2538 -> AgdaAny -> AgdaAny
du_'43''45'inverse'737'_2636 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_'43''45'inverse_2558 (coe v0))
-- Algebra.Structures.IsNearring.+-inverseʳ
d_'43''45'inverse'691'_2638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> T_IsNearring_2538 -> AgdaAny -> AgdaAny
d_'43''45'inverse'691'_2638 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'43''45'inverse'691'_2638 v9
du_'43''45'inverse'691'_2638 ::
  T_IsNearring_2538 -> AgdaAny -> AgdaAny
du_'43''45'inverse'691'_2638 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_'43''45'inverse_2558 (coe v0))
-- Algebra.Structures.IsRing
d_IsRing_2650 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsRing_2650
  = C_IsRing'46'constructor_95033 T_IsAbelianGroup_1132
                                  (AgdaAny ->
                                   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2672 ::
  T_IsRing_2650 -> T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_2672 v0
  = case coe v0 of
      C_IsRing'46'constructor_95033 v1 v2 v3 v4 v5 -> coe v1
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRing.*-cong
d_'42''45'cong_2674 ::
  T_IsRing_2650 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2674 v0
  = case coe v0 of
      C_IsRing'46'constructor_95033 v1 v2 v3 v4 v5 -> coe v2
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRing.*-assoc
d_'42''45'assoc_2676 ::
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2676 v0
  = case coe v0 of
      C_IsRing'46'constructor_95033 v1 v2 v3 v4 v5 -> coe v3
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRing.*-identity
d_'42''45'identity_2678 ::
  T_IsRing_2650 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2678 v0
  = case coe v0 of
      C_IsRing'46'constructor_95033 v1 v2 v3 v4 v5 -> coe v4
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRing.distrib
d_distrib_2680 ::
  T_IsRing_2650 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2680 v0
  = case coe v0 of
      C_IsRing'46'constructor_95033 v1 v2 v3 v4 v5 -> coe v5
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRing.isRingWithoutOne
d_isRingWithoutOne_2682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsRingWithoutOne_2286
d_isRingWithoutOne_2682 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isRingWithoutOne_2682 v9
du_isRingWithoutOne_2682 ::
  T_IsRing_2650 -> T_IsRingWithoutOne_2286
du_isRingWithoutOne_2682 v0
  = coe
      C_IsRingWithoutOne'46'constructor_75855
      (coe d_'43''45'isAbelianGroup_2672 (coe v0))
      (coe d_'42''45'cong_2674 (coe v0))
      (coe d_'42''45'assoc_2676 (coe v0)) (coe d_distrib_2680 (coe v0))
-- Algebra.Structures.IsRing._._//_
d__'47''47'__2686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__2686 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du__'47''47'__2686 v4 v6
du__'47''47'__2686 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__2686 v0 v1 = coe du__'47''47'__1098 (coe v0) (coe v1)
-- Algebra.Structures.IsRing._.∙-congʳ
d_'8729''45'cong'691'_2688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2688 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2688 v9
du_'8729''45'cong'691'_2688 ::
  T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2688 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isSemigroup_2390 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsRing._.∙-congˡ
d_'8729''45'cong'737'_2690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2690 v9
du_'8729''45'cong'737'_2690 ::
  T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2690 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = coe du_'42''45'isSemigroup_2390 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v2))))
-- Algebra.Structures.IsRing._.*-isMagma
d_'42''45'isMagma_2692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsMagma_176
d_'42''45'isMagma_2692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMagma_2692 v9
du_'42''45'isMagma_2692 :: T_IsRing_2650 -> T_IsMagma_176
du_'42''45'isMagma_2692 v0
  = coe
      du_'42''45'isMagma_2388 (coe du_isRingWithoutOne_2682 (coe v0))
-- Algebra.Structures.IsRing._.*-isSemigroup
d_'42''45'isSemigroup_2694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsSemigroup_472
d_'42''45'isSemigroup_2694 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isSemigroup_2694 v9
du_'42''45'isSemigroup_2694 :: T_IsRing_2650 -> T_IsSemigroup_472
du_'42''45'isSemigroup_2694 v0
  = coe
      du_'42''45'isSemigroup_2390 (coe du_isRingWithoutOne_2682 (coe v0))
-- Algebra.Structures.IsRing._.assoc
d_assoc_2696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2696 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_assoc_2696 v9
du_assoc_2696 ::
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_2696 v0
  = coe
      d_assoc_482
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_1050
            (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0)))))
-- Algebra.Structures.IsRing._.comm
d_comm_2698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_comm_2698 v9
du_comm_2698 :: T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_2698 v0
  = coe d_comm_1146 (coe d_'43''45'isAbelianGroup_2672 (coe v0))
-- Algebra.Structures.IsRing._.∙-cong
d_'8729''45'cong_2700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong_2700 v9
du_'8729''45'cong_2700 ::
  T_IsRing_2650 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_2700 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_1050
               (coe
                  d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0))))))
-- Algebra.Structures.IsRing._.∙-congʳ
d_'8729''45'cong'691'_2702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2702 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2702 v9
du_'8729''45'cong'691'_2702 ::
  T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2702 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe
         (let v3 = d_isGroup_1144 (coe v2) in
          coe
            (let v4 = d_isMonoid_1050 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsRing._.∙-congˡ
d_'8729''45'cong'737'_2704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2704 v9
du_'8729''45'cong'737'_2704 ::
  T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2704 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe
         (let v3 = d_isGroup_1144 (coe v2) in
          coe
            (let v4 = d_isMonoid_1050 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsRing._.identity
d_identity_2706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2650 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity_2706 v9
du_identity_2706 ::
  T_IsRing_2650 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_2706 v0
  = coe
      d_identity_698
      (coe
         d_isMonoid_1050
         (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0))))
-- Algebra.Structures.IsRing._.identityʳ
d_identity'691'_2708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny
d_identity'691'_2708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2708 v9
du_identity'691'_2708 :: T_IsRing_2650 -> AgdaAny -> AgdaAny
du_identity'691'_2708 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe
         (let v3 = d_isGroup_1144 (coe v2) in
          coe (coe du_identity'691'_728 (coe d_isMonoid_1050 (coe v3)))))
-- Algebra.Structures.IsRing._.identityˡ
d_identity'737'_2710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny
d_identity'737'_2710 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2710 v9
du_identity'737'_2710 :: T_IsRing_2650 -> AgdaAny -> AgdaAny
du_identity'737'_2710 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe
         (let v3 = d_isGroup_1144 (coe v2) in
          coe (coe du_identity'737'_726 (coe d_isMonoid_1050 (coe v3)))))
-- Algebra.Structures.IsRing._.isCommutativeMagma
d_isCommutativeMagma_2712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_2712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_2712 v9
du_isCommutativeMagma_2712 ::
  T_IsRing_2650 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_2712 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe
         (let v3 = coe du_isCommutativeMonoid_1204 (coe v2) in
          coe
            (coe
               du_isCommutativeMagma_586
               (coe du_isCommutativeSemigroup_786 (coe v3)))))
-- Algebra.Structures.IsRing._.isCommutativeMonoid
d_isCommutativeMonoid_2714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsCommutativeMonoid_736
d_isCommutativeMonoid_2714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMonoid_2714 v9
du_isCommutativeMonoid_2714 ::
  T_IsRing_2650 -> T_IsCommutativeMonoid_736
du_isCommutativeMonoid_2714 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (coe
         du_isCommutativeMonoid_1204
         (coe d_'43''45'isAbelianGroup_2304 (coe v1)))
-- Algebra.Structures.IsRing._.isCommutativeSemigroup
d_isCommutativeSemigroup_2716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_2716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              v9
  = du_isCommutativeSemigroup_2716 v9
du_isCommutativeSemigroup_2716 ::
  T_IsRing_2650 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_2716 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe
         (coe
            du_isCommutativeSemigroup_786
            (coe du_isCommutativeMonoid_1204 (coe v2))))
-- Algebra.Structures.IsRing._.isGroup
d_isGroup_2718 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsGroup_1036
d_isGroup_2718 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isGroup_2718 v9
du_isGroup_2718 :: T_IsRing_2650 -> T_IsGroup_1036
du_isGroup_2718 v0
  = coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0))
-- Algebra.Structures.IsRing._.isInvertibleMagma
d_isInvertibleMagma_2720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsInvertibleMagma_924
d_isInvertibleMagma_2720 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isInvertibleMagma_2720 v9
du_isInvertibleMagma_2720 ::
  T_IsRing_2650 -> T_IsInvertibleMagma_924
du_isInvertibleMagma_2720 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe (coe du_isInvertibleMagma_1122 (coe d_isGroup_1144 (coe v2))))
-- Algebra.Structures.IsRing._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2650 -> T_IsInvertibleUnitalMagma_976
d_isInvertibleUnitalMagma_2722 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_isInvertibleUnitalMagma_2722 v9
du_isInvertibleUnitalMagma_2722 ::
  T_IsRing_2650 -> T_IsInvertibleUnitalMagma_976
du_isInvertibleUnitalMagma_2722 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe
         (coe
            du_isInvertibleUnitalMagma_1124 (coe d_isGroup_1144 (coe v2))))
-- Algebra.Structures.IsRing._.isMagma
d_isMagma_2724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsMagma_176
d_isMagma_2724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isMagma_2724 v9
du_isMagma_2724 :: T_IsRing_2650 -> T_IsMagma_176
du_isMagma_2724 v0
  = coe
      d_isMagma_480
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_1050
            (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0)))))
-- Algebra.Structures.IsRing._.isMonoid
d_isMonoid_2726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsMonoid_686
d_isMonoid_2726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isMonoid_2726 v9
du_isMonoid_2726 :: T_IsRing_2650 -> T_IsMonoid_686
du_isMonoid_2726 v0
  = coe
      d_isMonoid_1050
      (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0)))
-- Algebra.Structures.IsRing._.isSemigroup
d_isSemigroup_2728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsSemigroup_472
d_isSemigroup_2728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isSemigroup_2728 v9
du_isSemigroup_2728 :: T_IsRing_2650 -> T_IsSemigroup_472
du_isSemigroup_2728 v0
  = coe
      d_isSemigroup_696
      (coe
         d_isMonoid_1050
         (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0))))
-- Algebra.Structures.IsRing._.isUnitalMagma
d_isUnitalMagma_2730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsUnitalMagma_642
d_isUnitalMagma_2730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_2730 v9
du_isUnitalMagma_2730 :: T_IsRing_2650 -> T_IsUnitalMagma_642
du_isUnitalMagma_2730 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe
         (let v3 = d_isGroup_1144 (coe v2) in
          coe (coe du_isUnitalMagma_730 (coe d_isMonoid_1050 (coe v3)))))
-- Algebra.Structures.IsRing._.⁻¹-cong
d_'8315''185''45'cong_2732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_2732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8315''185''45'cong_2732 v9
du_'8315''185''45'cong_2732 ::
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'cong_2732 v0
  = coe
      d_'8315''185''45'cong_1054
      (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0)))
-- Algebra.Structures.IsRing._.inverse
d_inverse_2734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2650 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse_2734 v9
du_inverse_2734 ::
  T_IsRing_2650 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_2734 v0
  = coe
      d_inverse_1052
      (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0)))
-- Algebra.Structures.IsRing._.inverseʳ
d_inverse'691'_2736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny
d_inverse'691'_2736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'691'_2736 v9
du_inverse'691'_2736 :: T_IsRing_2650 -> AgdaAny -> AgdaAny
du_inverse'691'_2736 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe (coe du_inverse'691'_1108 (coe d_isGroup_1144 (coe v2))))
-- Algebra.Structures.IsRing._.inverseˡ
d_inverse'737'_2738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny
d_inverse'737'_2738 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'737'_2738 v9
du_inverse'737'_2738 :: T_IsRing_2650 -> AgdaAny -> AgdaAny
du_inverse'737'_2738 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe (coe du_inverse'737'_1106 (coe d_isGroup_1144 (coe v2))))
-- Algebra.Structures.IsRing._.distribʳ
d_distrib'691'_2740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'691'_2740 v9
du_distrib'691'_2740 ::
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2740 v0
  = coe du_distrib'691'_2380 (coe du_isRingWithoutOne_2682 (coe v0))
-- Algebra.Structures.IsRing._.distribˡ
d_distrib'737'_2742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2742 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'737'_2742 v9
du_distrib'737'_2742 ::
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2742 v0
  = coe du_distrib'737'_2378 (coe du_isRingWithoutOne_2682 (coe v0))
-- Algebra.Structures.IsRing._.isEquivalence
d_isEquivalence_2744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2744 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_2744 v9
du_isEquivalence_2744 ::
  T_IsRing_2650 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_2744 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_1050
               (coe
                  d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0))))))
-- Algebra.Structures.IsRing._.isPartialEquivalence
d_isPartialEquivalence_2746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2746 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_2746 v9
du_isPartialEquivalence_2746 ::
  T_IsRing_2650 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2746 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe
         (let v3 = d_isGroup_1144 (coe v2) in
          coe
            (let v4 = d_isMonoid_1050 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (let v6 = d_isMagma_480 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                        (coe d_isEquivalence_184 (coe v6))))))))
-- Algebra.Structures.IsRing._.refl
d_refl_2748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny
d_refl_2748 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_refl_2748 v9
du_refl_2748 :: T_IsRing_2650 -> AgdaAny -> AgdaAny
du_refl_2748 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0)))))))
-- Algebra.Structures.IsRing._.reflexive
d_reflexive_2750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_2750 v9
du_reflexive_2750 ::
  T_IsRing_2650 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2750 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe
         (let v3 = d_isGroup_1144 (coe v2) in
          coe
            (let v4 = d_isMonoid_1050 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe
                  (let v6 = d_isMagma_480 (coe v5) in
                   coe
                     (\ v7 v8 v9 ->
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                          (coe d_isEquivalence_184 (coe v6)) v7))))))
-- Algebra.Structures.IsRing._.setoid
d_setoid_2752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_2752 v9
du_setoid_2752 ::
  T_IsRing_2650 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2752 v0
  = let v1 = coe du_isRingWithoutOne_2682 (coe v0) in
    coe
      (let v2 = d_'43''45'isAbelianGroup_2304 (coe v1) in
       coe
         (let v3 = d_isGroup_1144 (coe v2) in
          coe
            (let v4 = d_isMonoid_1050 (coe v3) in
             coe
               (let v5 = d_isSemigroup_696 (coe v4) in
                coe (coe du_setoid_200 (coe d_isMagma_480 (coe v5)))))))
-- Algebra.Structures.IsRing._.sym
d_sym_2754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2754 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_2754 v9
du_sym_2754 ::
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2754 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0)))))))
-- Algebra.Structures.IsRing._.trans
d_trans_2756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_2756 v9
du_trans_2756 ::
  T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2756 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v0)))))))
-- Algebra.Structures.IsRing._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_2758 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'691''45''8315''185'_2758 v4 v6 v7 v9
du_unique'691''45''8315''185'_2758 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_2758 v0 v1 v2 v3
  = let v4 = coe du_isRingWithoutOne_2682 (coe v3) in
    coe
      (let v5 = d_'43''45'isAbelianGroup_2304 (coe v4) in
       coe
         (coe
            du_unique'691''45''8315''185'_1120 (coe v0) (coe v2) (coe v1)
            (coe d_isGroup_1144 (coe v5))))
-- Algebra.Structures.IsRing._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2760 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_2760 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'737''45''8315''185'_2760 v4 v6 v7 v9
du_unique'737''45''8315''185'_2760 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRing_2650 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_2760 v0 v1 v2 v3
  = let v4 = coe du_isRingWithoutOne_2682 (coe v3) in
    coe
      (let v5 = d_'43''45'isAbelianGroup_2304 (coe v4) in
       coe
         (coe
            du_unique'737''45''8315''185'_1114 (coe v0) (coe v2) (coe v1)
            (coe d_isGroup_1144 (coe v5))))
-- Algebra.Structures.IsRing._.zero
d_zero_2762 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsRing_2650 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2762 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero_2762 v4 v5 v6 v7 v9
du_zero_2762 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2650 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_2762 v0 v1 v2 v3 v4
  = coe
      du_zero_2386 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_isRingWithoutOne_2682 (coe v4))
-- Algebra.Structures.IsRing._.zeroʳ
d_zero'691'_2764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny
d_zero'691'_2764 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'691'_2764 v4 v5 v6 v7 v9
du_zero'691'_2764 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny
du_zero'691'_2764 v0 v1 v2 v3 v4
  = coe
      du_zero'691'_2384 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_isRingWithoutOne_2682 (coe v4))
-- Algebra.Structures.IsRing._.zeroˡ
d_zero'737'_2766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny
d_zero'737'_2766 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'737'_2766 v4 v5 v6 v7 v9
du_zero'737'_2766 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny
du_zero'737'_2766 v0 v1 v2 v3 v4
  = coe
      du_zero'737'_2382 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_isRingWithoutOne_2682 (coe v4))
-- Algebra.Structures.IsRing.*-isMonoid
d_'42''45'isMonoid_2768 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsMonoid_686
d_'42''45'isMonoid_2768 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMonoid_2768 v9
du_'42''45'isMonoid_2768 :: T_IsRing_2650 -> T_IsMonoid_686
du_'42''45'isMonoid_2768 v0
  = coe
      C_IsMonoid'46'constructor_15873
      (coe
         du_'42''45'isSemigroup_2390
         (coe du_isRingWithoutOne_2682 (coe v0)))
      (coe d_'42''45'identity_2678 (coe v0))
-- Algebra.Structures.IsRing._.identityʳ
d_identity'691'_2772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny
d_identity'691'_2772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2772 v9
du_identity'691'_2772 :: T_IsRing_2650 -> AgdaAny -> AgdaAny
du_identity'691'_2772 v0
  = coe du_identity'691'_728 (coe du_'42''45'isMonoid_2768 (coe v0))
-- Algebra.Structures.IsRing._.identityˡ
d_identity'737'_2774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> AgdaAny -> AgdaAny
d_identity'737'_2774 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2774 v9
du_identity'737'_2774 :: T_IsRing_2650 -> AgdaAny -> AgdaAny
du_identity'737'_2774 v0
  = coe du_identity'737'_726 (coe du_'42''45'isMonoid_2768 (coe v0))
-- Algebra.Structures.IsRing.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing_2650 -> T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_2776 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                         ~v6 ~v7 ~v8 v9
  = du_isSemiringWithoutAnnihilatingZero_2776 v9
du_isSemiringWithoutAnnihilatingZero_2776 ::
  T_IsRing_2650 -> T_IsSemiringWithoutAnnihilatingZero_1468
du_isSemiringWithoutAnnihilatingZero_2776 v0
  = coe
      C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811
      (coe
         du_isCommutativeMonoid_1204
         (coe d_'43''45'isAbelianGroup_2672 (coe v0)))
      (coe d_'42''45'cong_2674 (coe v0))
      (coe d_'42''45'assoc_2676 (coe v0))
      (coe d_'42''45'identity_2678 (coe v0))
      (coe d_distrib_2680 (coe v0))
-- Algebra.Structures.IsRing.isSemiring
d_isSemiring_2778 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsSemiring_1570
d_isSemiring_2778 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isSemiring_2778 v4 v5 v6 v7 v9
du_isSemiring_2778 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2650 -> T_IsSemiring_1570
du_isSemiring_2778 v0 v1 v2 v3 v4
  = coe
      C_IsSemiring'46'constructor_48071
      (coe du_isSemiringWithoutAnnihilatingZero_2776 (coe v4))
      (coe
         du_zero_2386 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe du_isRingWithoutOne_2682 (coe v4)))
-- Algebra.Structures.IsRing._.isNearSemiring
d_isNearSemiring_2782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsNearSemiring_1218
d_isNearSemiring_2782 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isNearSemiring_2782 v4 v5 v6 v7 v9
du_isNearSemiring_2782 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2650 -> T_IsNearSemiring_1218
du_isNearSemiring_2782 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_isSemiring_2778 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) in
    coe
      (coe
         du_isNearSemiring_1374 (coe du_isSemiringWithoutOne_1660 (coe v5)))
-- Algebra.Structures.IsRing._.isSemiringWithoutOne
d_isSemiringWithoutOne_2784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing_2650 -> T_IsSemiringWithoutOne_1298
d_isSemiringWithoutOne_2784 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isSemiringWithoutOne_2784 v4 v5 v6 v7 v9
du_isSemiringWithoutOne_2784 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRing_2650 -> T_IsSemiringWithoutOne_1298
du_isSemiringWithoutOne_2784 v0 v1 v2 v3 v4
  = coe
      du_isSemiringWithoutOne_1660
      (coe
         du_isSemiring_2778 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Structures.IsCommutativeRing
d_IsCommutativeRing_2796 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsCommutativeRing_2796
  = C_IsCommutativeRing'46'constructor_100945 T_IsRing_2650
                                              (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsCommutativeRing.isRing
d_isRing_2812 :: T_IsCommutativeRing_2796 -> T_IsRing_2650
d_isRing_2812 v0
  = case coe v0 of
      C_IsCommutativeRing'46'constructor_100945 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeRing.*-comm
d_'42''45'comm_2814 ::
  T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_2814 v0
  = case coe v0 of
      C_IsCommutativeRing'46'constructor_100945 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsCommutativeRing._._//_
d__'47''47'__2818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__2818 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du__'47''47'__2818 v4 v6
du__'47''47'__2818 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__2818 v0 v1 = coe du__'47''47'__1098 (coe v0) (coe v1)
-- Algebra.Structures.IsCommutativeRing._.*-assoc
d_'42''45'assoc_2820 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2820 v0
  = coe d_'42''45'assoc_2676 (coe d_isRing_2812 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.*-cong
d_'42''45'cong_2822 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2822 v0
  = coe d_'42''45'cong_2674 (coe d_isRing_2812 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_2824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2824 v9
du_'8729''45'cong'691'_2824 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2824 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = coe du_'42''45'isSemigroup_2390 (coe v2) in
          coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_2826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2826 v9
du_'8729''45'cong'737'_2826 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2826 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = coe du_'42''45'isSemigroup_2390 (coe v2) in
          coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.*-identity
d_'42''45'identity_2828 ::
  T_IsCommutativeRing_2796 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2828 v0
  = coe d_'42''45'identity_2678 (coe d_isRing_2812 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.identityʳ
d_identity'691'_2830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
d_identity'691'_2830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2830 v9
du_identity'691'_2830 ::
  T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
du_identity'691'_2830 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe du_identity'691'_728 (coe du_'42''45'isMonoid_2768 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.identityˡ
d_identity'737'_2832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
d_identity'737'_2832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2832 v9
du_identity'737'_2832 ::
  T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
du_identity'737'_2832 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe du_identity'737'_726 (coe du_'42''45'isMonoid_2768 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.*-isMagma
d_'42''45'isMagma_2834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2796 -> T_IsMagma_176
d_'42''45'isMagma_2834 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMagma_2834 v9
du_'42''45'isMagma_2834 ::
  T_IsCommutativeRing_2796 -> T_IsMagma_176
du_'42''45'isMagma_2834 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         du_'42''45'isMagma_2388 (coe du_isRingWithoutOne_2682 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.*-isMonoid
d_'42''45'isMonoid_2836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2796 -> T_IsMonoid_686
d_'42''45'isMonoid_2836 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isMonoid_2836 v9
du_'42''45'isMonoid_2836 ::
  T_IsCommutativeRing_2796 -> T_IsMonoid_686
du_'42''45'isMonoid_2836 v0
  = coe du_'42''45'isMonoid_2768 (coe d_isRing_2812 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.*-isSemigroup
d_'42''45'isSemigroup_2838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2796 -> T_IsSemigroup_472
d_'42''45'isSemigroup_2838 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'42''45'isSemigroup_2838 v9
du_'42''45'isSemigroup_2838 ::
  T_IsCommutativeRing_2796 -> T_IsSemigroup_472
du_'42''45'isSemigroup_2838 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         du_'42''45'isSemigroup_2390
         (coe du_isRingWithoutOne_2682 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.assoc
d_assoc_2840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2840 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_assoc_2840 v9
du_assoc_2840 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_2840 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         d_assoc_482
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_1050
               (coe
                  d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1))))))
-- Algebra.Structures.IsCommutativeRing._.comm
d_comm_2842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2842 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_comm_2842 v9
du_comm_2842 ::
  T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_2842 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe (coe d_comm_1146 (coe d_'43''45'isAbelianGroup_2672 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.∙-cong
d_'8729''45'cong_2844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2844 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong_2844 v9
du_'8729''45'cong_2844 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_2844 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         d_'8729''45'cong_186
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1)))))))
-- Algebra.Structures.IsCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_2846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2846 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_2846 v9
du_'8729''45'cong'691'_2846 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2846 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe
            (let v4 = d_isGroup_1144 (coe v3) in
             coe
               (let v5 = d_isMonoid_1050 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (coe du_'8729''45'cong'691'_206 (coe d_isMagma_480 (coe v6))))))))
-- Algebra.Structures.IsCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_2848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2848 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_2848 v9
du_'8729''45'cong'737'_2848 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2848 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe
            (let v4 = d_isGroup_1144 (coe v3) in
             coe
               (let v5 = d_isMonoid_1050 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (coe du_'8729''45'cong'737'_202 (coe d_isMagma_480 (coe v6))))))))
-- Algebra.Structures.IsCommutativeRing._.identity
d_identity_2850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2850 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity_2850 v9
du_identity_2850 ::
  T_IsCommutativeRing_2796 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_2850 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         d_identity_698
         (coe
            d_isMonoid_1050
            (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1)))))
-- Algebra.Structures.IsCommutativeRing._.identityʳ
d_identity'691'_2852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
d_identity'691'_2852 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_2852 v9
du_identity'691'_2852 ::
  T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
du_identity'691'_2852 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe
            (let v4 = d_isGroup_1144 (coe v3) in
             coe (coe du_identity'691'_728 (coe d_isMonoid_1050 (coe v4))))))
-- Algebra.Structures.IsCommutativeRing._.identityˡ
d_identity'737'_2854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
d_identity'737'_2854 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_2854 v9
du_identity'737'_2854 ::
  T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
du_identity'737'_2854 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe
            (let v4 = d_isGroup_1144 (coe v3) in
             coe (coe du_identity'737'_726 (coe d_isMonoid_1050 (coe v4))))))
-- Algebra.Structures.IsCommutativeRing._.+-isAbelianGroup
d_'43''45'isAbelianGroup_2856 ::
  T_IsCommutativeRing_2796 -> T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_2856 v0
  = coe d_'43''45'isAbelianGroup_2672 (coe d_isRing_2812 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_2858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_2858 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_2858 v9
du_isCommutativeMagma_2858 ::
  T_IsCommutativeRing_2796 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_2858 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe
            (let v4 = coe du_isCommutativeMonoid_1204 (coe v3) in
             coe
               (coe
                  du_isCommutativeMagma_586
                  (coe du_isCommutativeSemigroup_786 (coe v4))))))
-- Algebra.Structures.IsCommutativeRing._.isCommutativeMonoid
d_isCommutativeMonoid_2860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsCommutativeMonoid_736
d_isCommutativeMonoid_2860 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMonoid_2860 v9
du_isCommutativeMonoid_2860 ::
  T_IsCommutativeRing_2796 -> T_IsCommutativeMonoid_736
du_isCommutativeMonoid_2860 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (coe
            du_isCommutativeMonoid_1204
            (coe d_'43''45'isAbelianGroup_2304 (coe v2))))
-- Algebra.Structures.IsCommutativeRing._.isCommutativeSemigroup
d_isCommutativeSemigroup_2862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_2862 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              v9
  = du_isCommutativeSemigroup_2862 v9
du_isCommutativeSemigroup_2862 ::
  T_IsCommutativeRing_2796 -> T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_2862 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe
            (coe
               du_isCommutativeSemigroup_786
               (coe du_isCommutativeMonoid_1204 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.isGroup
d_isGroup_2864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2796 -> T_IsGroup_1036
d_isGroup_2864 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isGroup_2864 v9
du_isGroup_2864 :: T_IsCommutativeRing_2796 -> T_IsGroup_1036
du_isGroup_2864 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.isInvertibleMagma
d_isInvertibleMagma_2866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsInvertibleMagma_924
d_isInvertibleMagma_2866 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isInvertibleMagma_2866 v9
du_isInvertibleMagma_2866 ::
  T_IsCommutativeRing_2796 -> T_IsInvertibleMagma_924
du_isInvertibleMagma_2866 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe (coe du_isInvertibleMagma_1122 (coe d_isGroup_1144 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 -> T_IsInvertibleUnitalMagma_976
d_isInvertibleUnitalMagma_2868 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_isInvertibleUnitalMagma_2868 v9
du_isInvertibleUnitalMagma_2868 ::
  T_IsCommutativeRing_2796 -> T_IsInvertibleUnitalMagma_976
du_isInvertibleUnitalMagma_2868 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe
            (coe
               du_isInvertibleUnitalMagma_1124 (coe d_isGroup_1144 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.isMagma
d_isMagma_2870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2796 -> T_IsMagma_176
d_isMagma_2870 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isMagma_2870 v9
du_isMagma_2870 :: T_IsCommutativeRing_2796 -> T_IsMagma_176
du_isMagma_2870 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         d_isMagma_480
         (coe
            d_isSemigroup_696
            (coe
               d_isMonoid_1050
               (coe
                  d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1))))))
-- Algebra.Structures.IsCommutativeRing._.isMonoid
d_isMonoid_2872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2796 -> T_IsMonoid_686
d_isMonoid_2872 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isMonoid_2872 v9
du_isMonoid_2872 :: T_IsCommutativeRing_2796 -> T_IsMonoid_686
du_isMonoid_2872 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         d_isMonoid_1050
         (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1))))
-- Algebra.Structures.IsCommutativeRing._.isSemigroup
d_isSemigroup_2874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2796 -> T_IsSemigroup_472
d_isSemigroup_2874 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isSemigroup_2874 v9
du_isSemigroup_2874 ::
  T_IsCommutativeRing_2796 -> T_IsSemigroup_472
du_isSemigroup_2874 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         d_isSemigroup_696
         (coe
            d_isMonoid_1050
            (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1)))))
-- Algebra.Structures.IsCommutativeRing._.isUnitalMagma
d_isUnitalMagma_2876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsUnitalMagma_642
d_isUnitalMagma_2876 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_2876 v9
du_isUnitalMagma_2876 ::
  T_IsCommutativeRing_2796 -> T_IsUnitalMagma_642
du_isUnitalMagma_2876 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe
            (let v4 = d_isGroup_1144 (coe v3) in
             coe (coe du_isUnitalMagma_730 (coe d_isMonoid_1050 (coe v4))))))
-- Algebra.Structures.IsCommutativeRing._.⁻¹-cong
d_'8315''185''45'cong_2878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_2878 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8315''185''45'cong_2878 v9
du_'8315''185''45'cong_2878 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'cong_2878 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         d_'8315''185''45'cong_1054
         (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1))))
-- Algebra.Structures.IsCommutativeRing._.inverse
d_inverse_2880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2880 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse_2880 v9
du_inverse_2880 ::
  T_IsCommutativeRing_2796 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_2880 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         d_inverse_1052
         (coe d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1))))
-- Algebra.Structures.IsCommutativeRing._.inverseʳ
d_inverse'691'_2882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
d_inverse'691'_2882 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'691'_2882 v9
du_inverse'691'_2882 ::
  T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
du_inverse'691'_2882 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe (coe du_inverse'691'_1108 (coe d_isGroup_1144 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.inverseˡ
d_inverse'737'_2884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
d_inverse'737'_2884 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'737'_2884 v9
du_inverse'737'_2884 ::
  T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
du_inverse'737'_2884 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe (coe du_inverse'737'_1106 (coe d_isGroup_1144 (coe v3)))))
-- Algebra.Structures.IsCommutativeRing._.distrib
d_distrib_2886 ::
  T_IsCommutativeRing_2796 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2886 v0 = coe d_distrib_2680 (coe d_isRing_2812 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.distribʳ
d_distrib'691'_2888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2888 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'691'_2888 v9
du_distrib'691'_2888 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_2888 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe du_distrib'691'_2380 (coe du_isRingWithoutOne_2682 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.distribˡ
d_distrib'737'_2890 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_2890 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_distrib'737'_2890 v9
du_distrib'737'_2890 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_2890 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe du_distrib'737'_2378 (coe du_isRingWithoutOne_2682 (coe v1)))
-- Algebra.Structures.IsCommutativeRing._.isEquivalence
d_isEquivalence_2892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2892 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_2892 v9
du_isEquivalence_2892 ::
  T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_2892 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_480
            (coe
               d_isSemigroup_696
               (coe
                  d_isMonoid_1050
                  (coe
                     d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1)))))))
-- Algebra.Structures.IsCommutativeRing._.isNearSemiring
d_isNearSemiring_2894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsNearSemiring_1218
d_isNearSemiring_2894 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isNearSemiring_2894 v4 v5 v6 v7 v9
du_isNearSemiring_2894 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsNearSemiring_1218
du_isNearSemiring_2894 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2812 (coe v4) in
    coe
      (let v6
             = coe
                 du_isSemiring_2778 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) in
       coe
         (coe
            du_isNearSemiring_1374
            (coe du_isSemiringWithoutOne_1660 (coe v6))))
-- Algebra.Structures.IsCommutativeRing._.isPartialEquivalence
d_isPartialEquivalence_2896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2896 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_2896 v9
du_isPartialEquivalence_2896 ::
  T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2896 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe
            (let v4 = d_isGroup_1144 (coe v3) in
             coe
               (let v5 = d_isMonoid_1050 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (let v7 = d_isMagma_480 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                           (coe d_isEquivalence_184 (coe v7)))))))))
-- Algebra.Structures.IsCommutativeRing._.isRingWithoutOne
d_isRingWithoutOne_2898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsRingWithoutOne_2286
d_isRingWithoutOne_2898 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isRingWithoutOne_2898 v9
du_isRingWithoutOne_2898 ::
  T_IsCommutativeRing_2796 -> T_IsRingWithoutOne_2286
du_isRingWithoutOne_2898 v0
  = coe du_isRingWithoutOne_2682 (coe d_isRing_2812 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.isSemiring
d_isSemiring_2900 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsCommutativeRing_2796 -> T_IsSemiring_1570
d_isSemiring_2900 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isSemiring_2900 v4 v5 v6 v7 v9
du_isSemiring_2900 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsSemiring_1570
du_isSemiring_2900 v0 v1 v2 v3 v4
  = coe
      du_isSemiring_2778 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe d_isRing_2812 (coe v4))
-- Algebra.Structures.IsCommutativeRing._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2902 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_2902 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                         ~v6 ~v7 ~v8 v9
  = du_isSemiringWithoutAnnihilatingZero_2902 v9
du_isSemiringWithoutAnnihilatingZero_2902 ::
  T_IsCommutativeRing_2796 ->
  T_IsSemiringWithoutAnnihilatingZero_1468
du_isSemiringWithoutAnnihilatingZero_2902 v0
  = coe
      du_isSemiringWithoutAnnihilatingZero_2776
      (coe d_isRing_2812 (coe v0))
-- Algebra.Structures.IsCommutativeRing._.isSemiringWithoutOne
d_isSemiringWithoutOne_2904 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsSemiringWithoutOne_1298
d_isSemiringWithoutOne_2904 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isSemiringWithoutOne_2904 v4 v5 v6 v7 v9
du_isSemiringWithoutOne_2904 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsSemiringWithoutOne_1298
du_isSemiringWithoutOne_2904 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2812 (coe v4) in
    coe
      (coe
         du_isSemiringWithoutOne_1660
         (coe
            du_isSemiring_2778 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)))
-- Algebra.Structures.IsCommutativeRing._.refl
d_refl_2906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
d_refl_2906 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_refl_2906 v9
du_refl_2906 :: T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
du_refl_2906 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            d_isEquivalence_184
            (coe
               d_isMagma_480
               (coe
                  d_isSemigroup_696
                  (coe
                     d_isMonoid_1050
                     (coe
                        d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1))))))))
-- Algebra.Structures.IsCommutativeRing._.reflexive
d_reflexive_2908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2908 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_2908 v9
du_reflexive_2908 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2908 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe
            (let v4 = d_isGroup_1144 (coe v3) in
             coe
               (let v5 = d_isMonoid_1050 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe
                     (let v7 = d_isMagma_480 (coe v6) in
                      coe
                        (\ v8 v9 v10 ->
                           coe
                             MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                             (coe d_isEquivalence_184 (coe v7)) v8)))))))
-- Algebra.Structures.IsCommutativeRing._.setoid
d_setoid_2910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2910 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_2910 v9
du_setoid_2910 ::
  T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2910 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (let v2 = coe du_isRingWithoutOne_2682 (coe v1) in
       coe
         (let v3 = d_'43''45'isAbelianGroup_2304 (coe v2) in
          coe
            (let v4 = d_isGroup_1144 (coe v3) in
             coe
               (let v5 = d_isMonoid_1050 (coe v4) in
                coe
                  (let v6 = d_isSemigroup_696 (coe v5) in
                   coe (coe du_setoid_200 (coe d_isMagma_480 (coe v6))))))))
-- Algebra.Structures.IsCommutativeRing._.sym
d_sym_2912 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2912 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_2912 v9
du_sym_2912 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2912 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            d_isEquivalence_184
            (coe
               d_isMagma_480
               (coe
                  d_isSemigroup_696
                  (coe
                     d_isMonoid_1050
                     (coe
                        d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1))))))))
-- Algebra.Structures.IsCommutativeRing._.trans
d_trans_2914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2914 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_2914 v9
du_trans_2914 ::
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2914 v0
  = let v1 = d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            d_isEquivalence_184
            (coe
               d_isMagma_480
               (coe
                  d_isSemigroup_696
                  (coe
                     d_isMonoid_1050
                     (coe
                        d_isGroup_1144 (coe d_'43''45'isAbelianGroup_2672 (coe v1))))))))
-- Algebra.Structures.IsCommutativeRing._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_2916 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'691''45''8315''185'_2916 v4 v6 v7 v9
du_unique'691''45''8315''185'_2916 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_2916 v0 v1 v2 v3
  = let v4 = d_isRing_2812 (coe v3) in
    coe
      (let v5 = coe du_isRingWithoutOne_2682 (coe v4) in
       coe
         (let v6 = d_'43''45'isAbelianGroup_2304 (coe v5) in
          coe
            (coe
               du_unique'691''45''8315''185'_1120 (coe v0) (coe v2) (coe v1)
               (coe d_isGroup_1144 (coe v6)))))
-- Algebra.Structures.IsCommutativeRing._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_2918 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'737''45''8315''185'_2918 v4 v6 v7 v9
du_unique'737''45''8315''185'_2918 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_2918 v0 v1 v2 v3
  = let v4 = d_isRing_2812 (coe v3) in
    coe
      (let v5 = coe du_isRingWithoutOne_2682 (coe v4) in
       coe
         (let v6 = d_'43''45'isAbelianGroup_2304 (coe v5) in
          coe
            (coe
               du_unique'737''45''8315''185'_1114 (coe v0) (coe v2) (coe v1)
               (coe d_isGroup_1144 (coe v6)))))
-- Algebra.Structures.IsCommutativeRing._.zero
d_zero_2920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2920 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero_2920 v4 v5 v6 v7 v9
du_zero_2920 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeRing_2796 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_2920 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2812 (coe v4) in
    coe
      (coe
         du_zero_2386 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe du_isRingWithoutOne_2682 (coe v5)))
-- Algebra.Structures.IsCommutativeRing._.zeroʳ
d_zero'691'_2922 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
d_zero'691'_2922 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'691'_2922 v4 v5 v6 v7 v9
du_zero'691'_2922 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
du_zero'691'_2922 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2812 (coe v4) in
    coe
      (coe
         du_zero'691'_2384 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe du_isRingWithoutOne_2682 (coe v5)))
-- Algebra.Structures.IsCommutativeRing._.zeroˡ
d_zero'737'_2924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
d_zero'737'_2924 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'737'_2924 v4 v5 v6 v7 v9
du_zero'737'_2924 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2796 -> AgdaAny -> AgdaAny
du_zero'737'_2924 v0 v1 v2 v3 v4
  = let v5 = d_isRing_2812 (coe v4) in
    coe
      (coe
         du_zero'737'_2382 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe du_isRingWithoutOne_2682 (coe v5)))
-- Algebra.Structures.IsCommutativeRing.isCommutativeSemiring
d_isCommutativeSemiring_2926 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsCommutativeSemiring_1678
d_isCommutativeSemiring_2926 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isCommutativeSemiring_2926 v4 v5 v6 v7 v9
du_isCommutativeSemiring_2926 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsCommutativeSemiring_1678
du_isCommutativeSemiring_2926 v0 v1 v2 v3 v4
  = coe
      C_IsCommutativeSemiring'46'constructor_51895
      (coe
         du_isSemiring_2778 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe d_isRing_2812 (coe v4)))
      (coe d_'42''45'comm_2814 (coe v4))
-- Algebra.Structures.IsCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_2930 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsCommutativeMagma_212
d_isCommutativeMagma_2930 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_isCommutativeMagma_2930 v4 v5 v6 v7 v9
du_isCommutativeMagma_2930 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsCommutativeMagma_212
du_isCommutativeMagma_2930 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_isCommutativeSemiring_2926 (coe v0) (coe v1) (coe v2) (coe v3)
              (coe v4) in
    coe
      (let v6 = coe du_isCommutativeSemiringWithoutOne_1780 (coe v5) in
       coe
         (coe
            du_isCommutativeMagma_586
            (coe du_'42''45'isCommutativeSemigroup_1454 (coe v6))))
-- Algebra.Structures.IsCommutativeRing._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_2932 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsCommutativeMonoid_736
d_'42''45'isCommutativeMonoid_2932 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8
                                   v9
  = du_'42''45'isCommutativeMonoid_2932 v4 v5 v6 v7 v9
du_'42''45'isCommutativeMonoid_2932 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsCommutativeMonoid_736
du_'42''45'isCommutativeMonoid_2932 v0 v1 v2 v3 v4
  = coe
      du_'42''45'isCommutativeMonoid_1788
      (coe
         du_isCommutativeSemiring_2926 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Algebra.Structures.IsCommutativeRing._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_2934 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsCommutativeSemigroup_548
d_'42''45'isCommutativeSemigroup_2934 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                      ~v8 v9
  = du_'42''45'isCommutativeSemigroup_2934 v4 v5 v6 v7 v9
du_'42''45'isCommutativeSemigroup_2934 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsCommutativeRing_2796 -> T_IsCommutativeSemigroup_548
du_'42''45'isCommutativeSemigroup_2934 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_isCommutativeSemiring_2926 (coe v0) (coe v1) (coe v2) (coe v3)
              (coe v4) in
    coe
      (coe
         du_'42''45'isCommutativeSemigroup_1454
         (coe du_isCommutativeSemiringWithoutOne_1780 (coe v5)))
-- Algebra.Structures.IsCommutativeRing._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_2936 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeRing_2796 -> T_IsCommutativeSemiringWithoutOne_1382
d_isCommutativeSemiringWithoutOne_2936 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                       ~v8 v9
  = du_isCommutativeSemiringWithoutOne_2936 v4 v5 v6 v7 v9
du_isCommutativeSemiringWithoutOne_2936 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeRing_2796 -> T_IsCommutativeSemiringWithoutOne_1382
du_isCommutativeSemiringWithoutOne_2936 v0 v1 v2 v3 v4
  = coe
      du_isCommutativeSemiringWithoutOne_1780
      (coe
         du_isCommutativeSemiring_2926 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Algebra.Structures.IsQuasigroup
d_IsQuasigroup_2944 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsQuasigroup_2944
  = C_IsQuasigroup'46'constructor_106057 T_IsMagma_176
                                         (AgdaAny ->
                                          AgdaAny ->
                                          AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                         (AgdaAny ->
                                          AgdaAny ->
                                          AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                         MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                         MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsQuasigroup.isMagma
d_isMagma_2962 :: T_IsQuasigroup_2944 -> T_IsMagma_176
d_isMagma_2962 v0
  = case coe v0 of
      C_IsQuasigroup'46'constructor_106057 v1 v2 v3 v4 v5 -> coe v1
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasigroup.\\-cong
d_'92''92''45'cong_2964 ::
  T_IsQuasigroup_2944 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_2964 v0
  = case coe v0 of
      C_IsQuasigroup'46'constructor_106057 v1 v2 v3 v4 v5 -> coe v2
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasigroup.//-cong
d_'47''47''45'cong_2966 ::
  T_IsQuasigroup_2944 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_2966 v0
  = case coe v0 of
      C_IsQuasigroup'46'constructor_106057 v1 v2 v3 v4 v5 -> coe v3
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasigroup.leftDivides
d_leftDivides_2968 ::
  T_IsQuasigroup_2944 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_2968 v0
  = case coe v0 of
      C_IsQuasigroup'46'constructor_106057 v1 v2 v3 v4 v5 -> coe v4
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasigroup.rightDivides
d_rightDivides_2970 ::
  T_IsQuasigroup_2944 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_2970 v0
  = case coe v0 of
      C_IsQuasigroup'46'constructor_106057 v1 v2 v3 v4 v5 -> coe v5
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsQuasigroup._.isEquivalence
d_isEquivalence_2974 ::
  T_IsQuasigroup_2944 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2974 v0
  = coe d_isEquivalence_184 (coe d_isMagma_2962 (coe v0))
-- Algebra.Structures.IsQuasigroup._.isPartialEquivalence
d_isPartialEquivalence_2976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2976 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_2976 v7
du_isPartialEquivalence_2976 ::
  T_IsQuasigroup_2944 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2976 v0
  = let v1 = d_isMagma_2962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_184 (coe v1)))
-- Algebra.Structures.IsQuasigroup._.refl
d_refl_2978 :: T_IsQuasigroup_2944 -> AgdaAny -> AgdaAny
d_refl_2978 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_184 (coe d_isMagma_2962 (coe v0)))
-- Algebra.Structures.IsQuasigroup._.reflexive
d_reflexive_2980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2980 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_2980 v7
du_reflexive_2980 ::
  T_IsQuasigroup_2944 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2980 v0
  = let v1 = d_isMagma_2962 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_184 (coe v1)) v2)
-- Algebra.Structures.IsQuasigroup._.setoid
d_setoid_2982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2982 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_2982 v7
du_setoid_2982 ::
  T_IsQuasigroup_2944 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2982 v0 = coe du_setoid_200 (coe d_isMagma_2962 (coe v0))
-- Algebra.Structures.IsQuasigroup._.sym
d_sym_2984 ::
  T_IsQuasigroup_2944 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2984 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_184 (coe d_isMagma_2962 (coe v0)))
-- Algebra.Structures.IsQuasigroup._.trans
d_trans_2986 ::
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2986 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_184 (coe d_isMagma_2962 (coe v0)))
-- Algebra.Structures.IsQuasigroup._.∙-cong
d_'8729''45'cong_2988 ::
  T_IsQuasigroup_2944 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2988 v0
  = coe d_'8729''45'cong_186 (coe d_isMagma_2962 (coe v0))
-- Algebra.Structures.IsQuasigroup._.∙-congʳ
d_'8729''45'cong'691'_2990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2990 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_2990 v7
du_'8729''45'cong'691'_2990 ::
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2990 v0
  = coe du_'8729''45'cong'691'_206 (coe d_isMagma_2962 (coe v0))
-- Algebra.Structures.IsQuasigroup._.∙-congˡ
d_'8729''45'cong'737'_2992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2992 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_2992 v7
du_'8729''45'cong'737'_2992 ::
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2992 v0
  = coe du_'8729''45'cong'737'_202 (coe d_isMagma_2962 (coe v0))
-- Algebra.Structures.IsQuasigroup.\\-congˡ
d_'92''92''45'cong'737'_2994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_2994 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
                             v10 v11
  = du_'92''92''45'cong'737'_2994 v7 v8 v9 v10 v11
du_'92''92''45'cong'737'_2994 ::
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_2994 v0 v1 v2 v3 v4
  = coe
      d_'92''92''45'cong_2964 v0 v1 v1 v2 v3
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (d_isEquivalence_184 (coe d_isMagma_2962 (coe v0))) v1)
      v4
-- Algebra.Structures.IsQuasigroup.\\-congʳ
d_'92''92''45'cong'691'_2998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_2998 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
                             v10 v11
  = du_'92''92''45'cong'691'_2998 v7 v8 v9 v10 v11
du_'92''92''45'cong'691'_2998 ::
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_2998 v0 v1 v2 v3 v4
  = coe
      d_'92''92''45'cong_2964 v0 v2 v3 v1 v1 v4
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (d_isEquivalence_184 (coe d_isMagma_2962 (coe v0))) v1)
-- Algebra.Structures.IsQuasigroup.//-congˡ
d_'47''47''45'cong'737'_3002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
                             v10 v11
  = du_'47''47''45'cong'737'_3002 v7 v8 v9 v10 v11
du_'47''47''45'cong'737'_3002 ::
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3002 v0 v1 v2 v3 v4
  = coe
      d_'47''47''45'cong_2966 v0 v1 v1 v2 v3
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (d_isEquivalence_184 (coe d_isMagma_2962 (coe v0))) v1)
      v4
-- Algebra.Structures.IsQuasigroup.//-congʳ
d_'47''47''45'cong'691'_3006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3006 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
                             v10 v11
  = du_'47''47''45'cong'691'_3006 v7 v8 v9 v10 v11
du_'47''47''45'cong'691'_3006 ::
  T_IsQuasigroup_2944 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3006 v0 v1 v2 v3 v4
  = coe
      d_'47''47''45'cong_2966 v0 v2 v3 v1 v1 v4
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (d_isEquivalence_184 (coe d_isMagma_2962 (coe v0))) v1)
-- Algebra.Structures.IsQuasigroup.leftDividesˡ
d_leftDivides'737'_3010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3010 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_leftDivides'737'_3010 v7
du_leftDivides'737'_3010 ::
  T_IsQuasigroup_2944 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3010 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_leftDivides_2968 (coe v0))
-- Algebra.Structures.IsQuasigroup.leftDividesʳ
d_leftDivides'691'_3012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3012 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_leftDivides'691'_3012 v7
du_leftDivides'691'_3012 ::
  T_IsQuasigroup_2944 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3012 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_leftDivides_2968 (coe v0))
-- Algebra.Structures.IsQuasigroup.rightDividesˡ
d_rightDivides'737'_3014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3014 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_rightDivides'737'_3014 v7
du_rightDivides'737'_3014 ::
  T_IsQuasigroup_2944 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3014 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_rightDivides_2970 (coe v0))
-- Algebra.Structures.IsQuasigroup.rightDividesʳ
d_rightDivides'691'_3016 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasigroup_2944 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3016 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_rightDivides'691'_3016 v7
du_rightDivides'691'_3016 ::
  T_IsQuasigroup_2944 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3016 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_rightDivides_2970 (coe v0))
-- Algebra.Structures.IsLoop
d_IsLoop_3026 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsLoop_3026
  = C_IsLoop'46'constructor_111285 T_IsQuasigroup_2944
                                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.IsLoop.isQuasigroup
d_isQuasigroup_3040 :: T_IsLoop_3026 -> T_IsQuasigroup_2944
d_isQuasigroup_3040 v0
  = case coe v0 of
      C_IsLoop'46'constructor_111285 v1 v2 -> coe v1
      _                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsLoop.identity
d_identity_3042 ::
  T_IsLoop_3026 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3042 v0
  = case coe v0 of
      C_IsLoop'46'constructor_111285 v1 v2 -> coe v2
      _                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsLoop._.//-cong
d_'47''47''45'cong_3046 ::
  T_IsLoop_3026 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_3046 v0
  = coe d_'47''47''45'cong_2966 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.//-congʳ
d_'47''47''45'cong'691'_3048 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3048 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'691'_3048 v8
du_'47''47''45'cong'691'_3048 ::
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3048 v0
  = coe
      du_'47''47''45'cong'691'_3006 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.//-congˡ
d_'47''47''45'cong'737'_3050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3050 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'737'_3050 v8
du_'47''47''45'cong'737'_3050 ::
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3050 v0
  = coe
      du_'47''47''45'cong'737'_3002 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.\\-cong
d_'92''92''45'cong_3052 ::
  T_IsLoop_3026 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_3052 v0
  = coe d_'92''92''45'cong_2964 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.\\-congʳ
d_'92''92''45'cong'691'_3054 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_3054 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'691'_3054 v8
du_'92''92''45'cong'691'_3054 ::
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_3054 v0
  = coe
      du_'92''92''45'cong'691'_2998 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.\\-congˡ
d_'92''92''45'cong'737'_3056 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_3056 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'737'_3056 v8
du_'92''92''45'cong'737'_3056 ::
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_3056 v0
  = coe
      du_'92''92''45'cong'737'_2994 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.isEquivalence
d_isEquivalence_3058 ::
  T_IsLoop_3026 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_3058 v0
  = coe
      d_isEquivalence_184
      (coe d_isMagma_2962 (coe d_isQuasigroup_3040 (coe v0)))
-- Algebra.Structures.IsLoop._.isMagma
d_isMagma_3060 :: T_IsLoop_3026 -> T_IsMagma_176
d_isMagma_3060 v0
  = coe d_isMagma_2962 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.isPartialEquivalence
d_isPartialEquivalence_3062 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3026 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3062 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_3062 v8
du_isPartialEquivalence_3062 ::
  T_IsLoop_3026 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3062 v0
  = let v1 = d_isQuasigroup_3040 (coe v0) in
    coe
      (let v2 = d_isMagma_2962 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe d_isEquivalence_184 (coe v2))))
-- Algebra.Structures.IsLoop._.leftDivides
d_leftDivides_3064 ::
  T_IsLoop_3026 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_3064 v0
  = coe d_leftDivides_2968 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.leftDividesʳ
d_leftDivides'691'_3066 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3026 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3066 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'691'_3066 v8
du_leftDivides'691'_3066 ::
  T_IsLoop_3026 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3066 v0
  = coe du_leftDivides'691'_3012 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.leftDividesˡ
d_leftDivides'737'_3068 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3026 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3068 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'737'_3068 v8
du_leftDivides'737'_3068 ::
  T_IsLoop_3026 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3068 v0
  = coe du_leftDivides'737'_3010 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.refl
d_refl_3070 :: T_IsLoop_3026 -> AgdaAny -> AgdaAny
d_refl_3070 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe d_isMagma_2962 (coe d_isQuasigroup_3040 (coe v0))))
-- Algebra.Structures.IsLoop._.reflexive
d_reflexive_3072 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3026 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3072 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_3072 v8
du_reflexive_3072 ::
  T_IsLoop_3026 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3072 v0
  = let v1 = d_isQuasigroup_3040 (coe v0) in
    coe
      (let v2 = d_isMagma_2962 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe d_isEquivalence_184 (coe v2)) v3))
-- Algebra.Structures.IsLoop._.rightDivides
d_rightDivides_3074 ::
  T_IsLoop_3026 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_3074 v0
  = coe d_rightDivides_2970 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.rightDividesʳ
d_rightDivides'691'_3076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3026 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3076 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'691'_3076 v8
du_rightDivides'691'_3076 ::
  T_IsLoop_3026 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3076 v0
  = coe du_rightDivides'691'_3016 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.rightDividesˡ
d_rightDivides'737'_3078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3026 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3078 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'737'_3078 v8
du_rightDivides'737'_3078 ::
  T_IsLoop_3026 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3078 v0
  = coe du_rightDivides'737'_3014 (coe d_isQuasigroup_3040 (coe v0))
-- Algebra.Structures.IsLoop._.setoid
d_setoid_3080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3026 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_3080 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_3080 v8
du_setoid_3080 ::
  T_IsLoop_3026 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_3080 v0
  = let v1 = d_isQuasigroup_3040 (coe v0) in
    coe (coe du_setoid_200 (coe d_isMagma_2962 (coe v1)))
-- Algebra.Structures.IsLoop._.sym
d_sym_3082 ::
  T_IsLoop_3026 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3082 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe d_isMagma_2962 (coe d_isQuasigroup_3040 (coe v0))))
-- Algebra.Structures.IsLoop._.trans
d_trans_3084 ::
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3084 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe d_isMagma_2962 (coe d_isQuasigroup_3040 (coe v0))))
-- Algebra.Structures.IsLoop._.∙-cong
d_'8729''45'cong_3086 ::
  T_IsLoop_3026 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3086 v0
  = coe
      d_'8729''45'cong_186
      (coe d_isMagma_2962 (coe d_isQuasigroup_3040 (coe v0)))
-- Algebra.Structures.IsLoop._.∙-congʳ
d_'8729''45'cong'691'_3088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3088 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_3088 v8
du_'8729''45'cong'691'_3088 ::
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3088 v0
  = let v1 = d_isQuasigroup_3040 (coe v0) in
    coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_2962 (coe v1)))
-- Algebra.Structures.IsLoop._.∙-congˡ
d_'8729''45'cong'737'_3090 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3090 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_3090 v8
du_'8729''45'cong'737'_3090 ::
  T_IsLoop_3026 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3090 v0
  = let v1 = d_isQuasigroup_3040 (coe v0) in
    coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_2962 (coe v1)))
-- Algebra.Structures.IsLoop.identityˡ
d_identity'737'_3092 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3026 -> AgdaAny -> AgdaAny
d_identity'737'_3092 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_3092 v8
du_identity'737'_3092 :: T_IsLoop_3026 -> AgdaAny -> AgdaAny
du_identity'737'_3092 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_identity_3042 (coe v0))
-- Algebra.Structures.IsLoop.identityʳ
d_identity'691'_3094 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLoop_3026 -> AgdaAny -> AgdaAny
d_identity'691'_3094 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_3094 v8
du_identity'691'_3094 :: T_IsLoop_3026 -> AgdaAny -> AgdaAny
du_identity'691'_3094 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_identity_3042 (coe v0))
-- Algebra.Structures.IsLeftBolLoop
d_IsLeftBolLoop_3104 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsLeftBolLoop_3104
  = C_IsLeftBolLoop'46'constructor_114283 T_IsLoop_3026
                                          (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsLeftBolLoop.isLoop
d_isLoop_3118 :: T_IsLeftBolLoop_3104 -> T_IsLoop_3026
d_isLoop_3118 v0
  = case coe v0 of
      C_IsLeftBolLoop'46'constructor_114283 v1 v2 -> coe v1
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsLeftBolLoop.leftBol
d_leftBol_3120 ::
  T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_leftBol_3120 v0
  = case coe v0 of
      C_IsLeftBolLoop'46'constructor_114283 v1 v2 -> coe v2
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsLeftBolLoop._.//-cong
d_'47''47''45'cong_3124 ::
  T_IsLeftBolLoop_3104 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_3124 v0
  = coe
      d_'47''47''45'cong_2966
      (coe d_isQuasigroup_3040 (coe d_isLoop_3118 (coe v0)))
-- Algebra.Structures.IsLeftBolLoop._.//-congʳ
d_'47''47''45'cong'691'_3126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'691'_3126 v8
du_'47''47''45'cong'691'_3126 ::
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3126 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'691'_3006 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.//-congˡ
d_'47''47''45'cong'737'_3128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'737'_3128 v8
du_'47''47''45'cong'737'_3128 ::
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3128 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'737'_3002 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.\\-cong
d_'92''92''45'cong_3130 ::
  T_IsLeftBolLoop_3104 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_3130 v0
  = coe
      d_'92''92''45'cong_2964
      (coe d_isQuasigroup_3040 (coe d_isLoop_3118 (coe v0)))
-- Algebra.Structures.IsLeftBolLoop._.\\-congʳ
d_'92''92''45'cong'691'_3132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_3132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'691'_3132 v8
du_'92''92''45'cong'691'_3132 ::
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_3132 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'691'_2998 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.\\-congˡ
d_'92''92''45'cong'737'_3134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_3134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'737'_3134 v8
du_'92''92''45'cong'737'_3134 ::
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_3134 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'737'_2994 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.identity
d_identity_3136 ::
  T_IsLeftBolLoop_3104 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3136 v0
  = coe d_identity_3042 (coe d_isLoop_3118 (coe v0))
-- Algebra.Structures.IsLeftBolLoop._.identityʳ
d_identity'691'_3138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny
d_identity'691'_3138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_3138 v8
du_identity'691'_3138 :: T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny
du_identity'691'_3138 v0
  = coe du_identity'691'_3094 (coe d_isLoop_3118 (coe v0))
-- Algebra.Structures.IsLeftBolLoop._.identityˡ
d_identity'737'_3140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny
d_identity'737'_3140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_3140 v8
du_identity'737'_3140 :: T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny
du_identity'737'_3140 v0
  = coe du_identity'737'_3092 (coe d_isLoop_3118 (coe v0))
-- Algebra.Structures.IsLeftBolLoop._.isEquivalence
d_isEquivalence_3142 ::
  T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_3142 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_2962
         (coe d_isQuasigroup_3040 (coe d_isLoop_3118 (coe v0))))
-- Algebra.Structures.IsLeftBolLoop._.isMagma
d_isMagma_3144 :: T_IsLeftBolLoop_3104 -> T_IsMagma_176
d_isMagma_3144 v0
  = coe
      d_isMagma_2962
      (coe d_isQuasigroup_3040 (coe d_isLoop_3118 (coe v0)))
-- Algebra.Structures.IsLeftBolLoop._.isPartialEquivalence
d_isPartialEquivalence_3146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_3146 v8
du_isPartialEquivalence_3146 ::
  T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3146 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe
         (let v3 = d_isMagma_2962 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.IsLeftBolLoop._.isQuasigroup
d_isQuasigroup_3148 :: T_IsLeftBolLoop_3104 -> T_IsQuasigroup_2944
d_isQuasigroup_3148 v0
  = coe d_isQuasigroup_3040 (coe d_isLoop_3118 (coe v0))
-- Algebra.Structures.IsLeftBolLoop._.leftDivides
d_leftDivides_3150 ::
  T_IsLeftBolLoop_3104 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_3150 v0
  = coe
      d_leftDivides_2968
      (coe d_isQuasigroup_3040 (coe d_isLoop_3118 (coe v0)))
-- Algebra.Structures.IsLeftBolLoop._.leftDividesʳ
d_leftDivides'691'_3152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'691'_3152 v8
du_leftDivides'691'_3152 ::
  T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3152 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (coe du_leftDivides'691'_3012 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.leftDividesˡ
d_leftDivides'737'_3154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'737'_3154 v8
du_leftDivides'737'_3154 ::
  T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3154 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (coe du_leftDivides'737'_3010 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.refl
d_refl_3156 :: T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny
d_refl_3156 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe d_isQuasigroup_3040 (coe d_isLoop_3118 (coe v0)))))
-- Algebra.Structures.IsLeftBolLoop._.reflexive
d_reflexive_3158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3104 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_3158 v8
du_reflexive_3158 ::
  T_IsLeftBolLoop_3104 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3158 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe
         (let v3 = d_isMagma_2962 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_184 (coe v3)) v4)))
-- Algebra.Structures.IsLeftBolLoop._.rightDivides
d_rightDivides_3160 ::
  T_IsLeftBolLoop_3104 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_3160 v0
  = coe
      d_rightDivides_2970
      (coe d_isQuasigroup_3040 (coe d_isLoop_3118 (coe v0)))
-- Algebra.Structures.IsLeftBolLoop._.rightDividesʳ
d_rightDivides'691'_3162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'691'_3162 v8
du_rightDivides'691'_3162 ::
  T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3162 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (coe du_rightDivides'691'_3016 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.rightDividesˡ
d_rightDivides'737'_3164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'737'_3164 v8
du_rightDivides'737'_3164 ::
  T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3164 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (coe du_rightDivides'737'_3014 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsLeftBolLoop._.setoid
d_setoid_3166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_3166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_3166 v8
du_setoid_3166 ::
  T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_3166 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe (coe du_setoid_200 (coe d_isMagma_2962 (coe v2))))
-- Algebra.Structures.IsLeftBolLoop._.sym
d_sym_3168 ::
  T_IsLeftBolLoop_3104 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3168 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe d_isQuasigroup_3040 (coe d_isLoop_3118 (coe v0)))))
-- Algebra.Structures.IsLeftBolLoop._.trans
d_trans_3170 ::
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3170 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe d_isQuasigroup_3040 (coe d_isLoop_3118 (coe v0)))))
-- Algebra.Structures.IsLeftBolLoop._.∙-cong
d_'8729''45'cong_3172 ::
  T_IsLeftBolLoop_3104 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3172 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_2962
         (coe d_isQuasigroup_3040 (coe d_isLoop_3118 (coe v0))))
-- Algebra.Structures.IsLeftBolLoop._.∙-congʳ
d_'8729''45'cong'691'_3174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3174 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_3174 v8
du_'8729''45'cong'691'_3174 ::
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3174 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_2962 (coe v2))))
-- Algebra.Structures.IsLeftBolLoop._.∙-congˡ
d_'8729''45'cong'737'_3176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_3176 v8
du_'8729''45'cong'737'_3176 ::
  T_IsLeftBolLoop_3104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3176 v0
  = let v1 = d_isLoop_3118 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_2962 (coe v2))))
-- Algebra.Structures.IsRightBolLoop
d_IsRightBolLoop_3186 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsRightBolLoop_3186
  = C_IsRightBolLoop'46'constructor_116761 T_IsLoop_3026
                                           (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsRightBolLoop.isLoop
d_isLoop_3200 :: T_IsRightBolLoop_3186 -> T_IsLoop_3026
d_isLoop_3200 v0
  = case coe v0 of
      C_IsRightBolLoop'46'constructor_116761 v1 v2 -> coe v1
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRightBolLoop.rightBol
d_rightBol_3202 ::
  T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_rightBol_3202 v0
  = case coe v0 of
      C_IsRightBolLoop'46'constructor_116761 v1 v2 -> coe v2
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsRightBolLoop._.//-cong
d_'47''47''45'cong_3206 ::
  T_IsRightBolLoop_3186 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_3206 v0
  = coe
      d_'47''47''45'cong_2966
      (coe d_isQuasigroup_3040 (coe d_isLoop_3200 (coe v0)))
-- Algebra.Structures.IsRightBolLoop._.//-congʳ
d_'47''47''45'cong'691'_3208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'691'_3208 v8
du_'47''47''45'cong'691'_3208 ::
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3208 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'691'_3006 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.//-congˡ
d_'47''47''45'cong'737'_3210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'737'_3210 v8
du_'47''47''45'cong'737'_3210 ::
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3210 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'737'_3002 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.\\-cong
d_'92''92''45'cong_3212 ::
  T_IsRightBolLoop_3186 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_3212 v0
  = coe
      d_'92''92''45'cong_2964
      (coe d_isQuasigroup_3040 (coe d_isLoop_3200 (coe v0)))
-- Algebra.Structures.IsRightBolLoop._.\\-congʳ
d_'92''92''45'cong'691'_3214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_3214 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'691'_3214 v8
du_'92''92''45'cong'691'_3214 ::
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_3214 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'691'_2998 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.\\-congˡ
d_'92''92''45'cong'737'_3216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_3216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'737'_3216 v8
du_'92''92''45'cong'737'_3216 ::
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_3216 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'737'_2994 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.identity
d_identity_3218 ::
  T_IsRightBolLoop_3186 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3218 v0
  = coe d_identity_3042 (coe d_isLoop_3200 (coe v0))
-- Algebra.Structures.IsRightBolLoop._.identityʳ
d_identity'691'_3220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny
d_identity'691'_3220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_3220 v8
du_identity'691'_3220 ::
  T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny
du_identity'691'_3220 v0
  = coe du_identity'691'_3094 (coe d_isLoop_3200 (coe v0))
-- Algebra.Structures.IsRightBolLoop._.identityˡ
d_identity'737'_3222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny
d_identity'737'_3222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_3222 v8
du_identity'737'_3222 ::
  T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny
du_identity'737'_3222 v0
  = coe du_identity'737'_3092 (coe d_isLoop_3200 (coe v0))
-- Algebra.Structures.IsRightBolLoop._.isEquivalence
d_isEquivalence_3224 ::
  T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_3224 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_2962
         (coe d_isQuasigroup_3040 (coe d_isLoop_3200 (coe v0))))
-- Algebra.Structures.IsRightBolLoop._.isMagma
d_isMagma_3226 :: T_IsRightBolLoop_3186 -> T_IsMagma_176
d_isMagma_3226 v0
  = coe
      d_isMagma_2962
      (coe d_isQuasigroup_3040 (coe d_isLoop_3200 (coe v0)))
-- Algebra.Structures.IsRightBolLoop._.isPartialEquivalence
d_isPartialEquivalence_3228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_3228 v8
du_isPartialEquivalence_3228 ::
  T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3228 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe
         (let v3 = d_isMagma_2962 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.IsRightBolLoop._.isQuasigroup
d_isQuasigroup_3230 :: T_IsRightBolLoop_3186 -> T_IsQuasigroup_2944
d_isQuasigroup_3230 v0
  = coe d_isQuasigroup_3040 (coe d_isLoop_3200 (coe v0))
-- Algebra.Structures.IsRightBolLoop._.leftDivides
d_leftDivides_3232 ::
  T_IsRightBolLoop_3186 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_3232 v0
  = coe
      d_leftDivides_2968
      (coe d_isQuasigroup_3040 (coe d_isLoop_3200 (coe v0)))
-- Algebra.Structures.IsRightBolLoop._.leftDividesʳ
d_leftDivides'691'_3234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'691'_3234 v8
du_leftDivides'691'_3234 ::
  T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3234 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (coe du_leftDivides'691'_3012 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.leftDividesˡ
d_leftDivides'737'_3236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'737'_3236 v8
du_leftDivides'737'_3236 ::
  T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3236 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (coe du_leftDivides'737'_3010 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.refl
d_refl_3238 :: T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny
d_refl_3238 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe d_isQuasigroup_3040 (coe d_isLoop_3200 (coe v0)))))
-- Algebra.Structures.IsRightBolLoop._.reflexive
d_reflexive_3240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3186 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_3240 v8
du_reflexive_3240 ::
  T_IsRightBolLoop_3186 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3240 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe
         (let v3 = d_isMagma_2962 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_184 (coe v3)) v4)))
-- Algebra.Structures.IsRightBolLoop._.rightDivides
d_rightDivides_3242 ::
  T_IsRightBolLoop_3186 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_3242 v0
  = coe
      d_rightDivides_2970
      (coe d_isQuasigroup_3040 (coe d_isLoop_3200 (coe v0)))
-- Algebra.Structures.IsRightBolLoop._.rightDividesʳ
d_rightDivides'691'_3244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'691'_3244 v8
du_rightDivides'691'_3244 ::
  T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3244 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (coe du_rightDivides'691'_3016 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.rightDividesˡ
d_rightDivides'737'_3246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'737'_3246 v8
du_rightDivides'737'_3246 ::
  T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3246 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (coe du_rightDivides'737'_3014 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsRightBolLoop._.setoid
d_setoid_3248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_3248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_3248 v8
du_setoid_3248 ::
  T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_3248 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe (coe du_setoid_200 (coe d_isMagma_2962 (coe v2))))
-- Algebra.Structures.IsRightBolLoop._.sym
d_sym_3250 ::
  T_IsRightBolLoop_3186 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3250 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe d_isQuasigroup_3040 (coe d_isLoop_3200 (coe v0)))))
-- Algebra.Structures.IsRightBolLoop._.trans
d_trans_3252 ::
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3252 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe d_isQuasigroup_3040 (coe d_isLoop_3200 (coe v0)))))
-- Algebra.Structures.IsRightBolLoop._.∙-cong
d_'8729''45'cong_3254 ::
  T_IsRightBolLoop_3186 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3254 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_2962
         (coe d_isQuasigroup_3040 (coe d_isLoop_3200 (coe v0))))
-- Algebra.Structures.IsRightBolLoop._.∙-congʳ
d_'8729''45'cong'691'_3256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_3256 v8
du_'8729''45'cong'691'_3256 ::
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3256 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_2962 (coe v2))))
-- Algebra.Structures.IsRightBolLoop._.∙-congˡ
d_'8729''45'cong'737'_3258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_3258 v8
du_'8729''45'cong'737'_3258 ::
  T_IsRightBolLoop_3186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3258 v0
  = let v1 = d_isLoop_3200 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_2962 (coe v2))))
-- Algebra.Structures.IsMoufangLoop
d_IsMoufangLoop_3268 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsMoufangLoop_3268
  = C_IsMoufangLoop'46'constructor_119263 T_IsLeftBolLoop_3104
                                          (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsMoufangLoop.isLeftBolLoop
d_isLeftBolLoop_3284 ::
  T_IsMoufangLoop_3268 -> T_IsLeftBolLoop_3104
d_isLeftBolLoop_3284 v0
  = case coe v0 of
      C_IsMoufangLoop'46'constructor_119263 v1 v2 v3 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMoufangLoop.rightBol
d_rightBol_3286 ::
  T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_rightBol_3286 v0
  = case coe v0 of
      C_IsMoufangLoop'46'constructor_119263 v1 v2 v3 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMoufangLoop.identical
d_identical_3288 ::
  T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identical_3288 v0
  = case coe v0 of
      C_IsMoufangLoop'46'constructor_119263 v1 v2 v3 -> coe v3
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMoufangLoop._.//-cong
d_'47''47''45'cong_3292 ::
  T_IsMoufangLoop_3268 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_3292 v0
  = coe
      d_'47''47''45'cong_2966
      (coe
         d_isQuasigroup_3040
         (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0))))
-- Algebra.Structures.IsMoufangLoop._.//-congʳ
d_'47''47''45'cong'691'_3294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'691'_3294 v8
du_'47''47''45'cong'691'_3294 ::
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3294 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (coe
            du_'47''47''45'cong'691'_3006 (coe d_isQuasigroup_3040 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.//-congˡ
d_'47''47''45'cong'737'_3296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'737'_3296 v8
du_'47''47''45'cong'737'_3296 ::
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3296 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (coe
            du_'47''47''45'cong'737'_3002 (coe d_isQuasigroup_3040 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.\\-cong
d_'92''92''45'cong_3298 ::
  T_IsMoufangLoop_3268 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_3298 v0
  = coe
      d_'92''92''45'cong_2964
      (coe
         d_isQuasigroup_3040
         (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0))))
-- Algebra.Structures.IsMoufangLoop._.\\-congʳ
d_'92''92''45'cong'691'_3300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_3300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'691'_3300 v8
du_'92''92''45'cong'691'_3300 ::
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_3300 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (coe
            du_'92''92''45'cong'691'_2998 (coe d_isQuasigroup_3040 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.\\-congˡ
d_'92''92''45'cong'737'_3302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_3302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'737'_3302 v8
du_'92''92''45'cong'737'_3302 ::
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_3302 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (coe
            du_'92''92''45'cong'737'_2994 (coe d_isQuasigroup_3040 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.identity
d_identity_3304 ::
  T_IsMoufangLoop_3268 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3304 v0
  = coe
      d_identity_3042
      (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0)))
-- Algebra.Structures.IsMoufangLoop._.identityʳ
d_identity'691'_3306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny
d_identity'691'_3306 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_3306 v8
du_identity'691'_3306 :: T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny
du_identity'691'_3306 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe (coe du_identity'691'_3094 (coe d_isLoop_3118 (coe v1)))
-- Algebra.Structures.IsMoufangLoop._.identityˡ
d_identity'737'_3308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny
d_identity'737'_3308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_3308 v8
du_identity'737'_3308 :: T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny
du_identity'737'_3308 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe (coe du_identity'737'_3092 (coe d_isLoop_3118 (coe v1)))
-- Algebra.Structures.IsMoufangLoop._.isEquivalence
d_isEquivalence_3310 ::
  T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_3310 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_2962
         (coe
            d_isQuasigroup_3040
            (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0)))))
-- Algebra.Structures.IsMoufangLoop._.isLoop
d_isLoop_3312 :: T_IsMoufangLoop_3268 -> T_IsLoop_3026
d_isLoop_3312 v0
  = coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0))
-- Algebra.Structures.IsMoufangLoop._.isMagma
d_isMagma_3314 :: T_IsMoufangLoop_3268 -> T_IsMagma_176
d_isMagma_3314 v0
  = coe
      d_isMagma_2962
      (coe
         d_isQuasigroup_3040
         (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0))))
-- Algebra.Structures.IsMoufangLoop._.isPartialEquivalence
d_isPartialEquivalence_3316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_3316 v8
du_isPartialEquivalence_3316 ::
  T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3316 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (let v3 = d_isQuasigroup_3040 (coe v2) in
          coe
            (let v4 = d_isMagma_2962 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe d_isEquivalence_184 (coe v4))))))
-- Algebra.Structures.IsMoufangLoop._.isQuasigroup
d_isQuasigroup_3318 :: T_IsMoufangLoop_3268 -> T_IsQuasigroup_2944
d_isQuasigroup_3318 v0
  = coe
      d_isQuasigroup_3040
      (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0)))
-- Algebra.Structures.IsMoufangLoop._.leftBol
d_leftBol_3320 ::
  T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_leftBol_3320 v0
  = coe d_leftBol_3120 (coe d_isLeftBolLoop_3284 (coe v0))
-- Algebra.Structures.IsMoufangLoop._.leftDivides
d_leftDivides_3322 ::
  T_IsMoufangLoop_3268 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_3322 v0
  = coe
      d_leftDivides_2968
      (coe
         d_isQuasigroup_3040
         (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0))))
-- Algebra.Structures.IsMoufangLoop._.leftDividesʳ
d_leftDivides'691'_3324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'691'_3324 v8
du_leftDivides'691'_3324 ::
  T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3324 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (coe du_leftDivides'691'_3012 (coe d_isQuasigroup_3040 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.leftDividesˡ
d_leftDivides'737'_3326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'737'_3326 v8
du_leftDivides'737'_3326 ::
  T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3326 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (coe du_leftDivides'737'_3010 (coe d_isQuasigroup_3040 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.refl
d_refl_3328 :: T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny
d_refl_3328 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe
               d_isQuasigroup_3040
               (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0))))))
-- Algebra.Structures.IsMoufangLoop._.reflexive
d_reflexive_3330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3268 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_3330 v8
du_reflexive_3330 ::
  T_IsMoufangLoop_3268 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3330 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (let v3 = d_isQuasigroup_3040 (coe v2) in
          coe
            (let v4 = d_isMagma_2962 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe d_isEquivalence_184 (coe v4)) v5))))
-- Algebra.Structures.IsMoufangLoop._.rightDivides
d_rightDivides_3332 ::
  T_IsMoufangLoop_3268 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_3332 v0
  = coe
      d_rightDivides_2970
      (coe
         d_isQuasigroup_3040
         (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0))))
-- Algebra.Structures.IsMoufangLoop._.rightDividesʳ
d_rightDivides'691'_3334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'691'_3334 v8
du_rightDivides'691'_3334 ::
  T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3334 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (coe du_rightDivides'691'_3016 (coe d_isQuasigroup_3040 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.rightDividesˡ
d_rightDivides'737'_3336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'737'_3336 v8
du_rightDivides'737'_3336 ::
  T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3336 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (coe du_rightDivides'737'_3014 (coe d_isQuasigroup_3040 (coe v2))))
-- Algebra.Structures.IsMoufangLoop._.setoid
d_setoid_3338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_3338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_3338 v8
du_setoid_3338 ::
  T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_3338 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (let v3 = d_isQuasigroup_3040 (coe v2) in
          coe (coe du_setoid_200 (coe d_isMagma_2962 (coe v3)))))
-- Algebra.Structures.IsMoufangLoop._.sym
d_sym_3340 ::
  T_IsMoufangLoop_3268 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3340 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe
               d_isQuasigroup_3040
               (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0))))))
-- Algebra.Structures.IsMoufangLoop._.trans
d_trans_3342 ::
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3342 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe
               d_isQuasigroup_3040
               (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0))))))
-- Algebra.Structures.IsMoufangLoop._.∙-cong
d_'8729''45'cong_3344 ::
  T_IsMoufangLoop_3268 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3344 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_2962
         (coe
            d_isQuasigroup_3040
            (coe d_isLoop_3118 (coe d_isLeftBolLoop_3284 (coe v0)))))
-- Algebra.Structures.IsMoufangLoop._.∙-congʳ
d_'8729''45'cong'691'_3346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_3346 v8
du_'8729''45'cong'691'_3346 ::
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3346 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (let v3 = d_isQuasigroup_3040 (coe v2) in
          coe
            (coe du_'8729''45'cong'691'_206 (coe d_isMagma_2962 (coe v3)))))
-- Algebra.Structures.IsMoufangLoop._.∙-congˡ
d_'8729''45'cong'737'_3348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_3348 v8
du_'8729''45'cong'737'_3348 ::
  T_IsMoufangLoop_3268 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3348 v0
  = let v1 = d_isLeftBolLoop_3284 (coe v0) in
    coe
      (let v2 = d_isLoop_3118 (coe v1) in
       coe
         (let v3 = d_isQuasigroup_3040 (coe v2) in
          coe
            (coe du_'8729''45'cong'737'_202 (coe d_isMagma_2962 (coe v3)))))
-- Algebra.Structures.IsMiddleBolLoop
d_IsMiddleBolLoop_3358 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsMiddleBolLoop_3358
  = C_IsMiddleBolLoop'46'constructor_121973 T_IsLoop_3026
                                            (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.IsMiddleBolLoop.isLoop
d_isLoop_3372 :: T_IsMiddleBolLoop_3358 -> T_IsLoop_3026
d_isLoop_3372 v0
  = case coe v0 of
      C_IsMiddleBolLoop'46'constructor_121973 v1 v2 -> coe v1
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMiddleBolLoop.middleBol
d_middleBol_3374 ::
  T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_middleBol_3374 v0
  = case coe v0 of
      C_IsMiddleBolLoop'46'constructor_121973 v1 v2 -> coe v2
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.IsMiddleBolLoop._.//-cong
d_'47''47''45'cong_3378 ::
  T_IsMiddleBolLoop_3358 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong_3378 v0
  = coe
      d_'47''47''45'cong_2966
      (coe d_isQuasigroup_3040 (coe d_isLoop_3372 (coe v0)))
-- Algebra.Structures.IsMiddleBolLoop._.//-congʳ
d_'47''47''45'cong'691'_3380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'691'_3380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'691'_3380 v8
du_'47''47''45'cong'691'_3380 ::
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'691'_3380 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'691'_3006 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.//-congˡ
d_'47''47''45'cong'737'_3382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'737'_3382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'47''47''45'cong'737'_3382 v8
du_'47''47''45'cong'737'_3382 ::
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'737'_3382 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (coe
         du_'47''47''45'cong'737'_3002 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.\\-cong
d_'92''92''45'cong_3384 ::
  T_IsMiddleBolLoop_3358 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong_3384 v0
  = coe
      d_'92''92''45'cong_2964
      (coe d_isQuasigroup_3040 (coe d_isLoop_3372 (coe v0)))
-- Algebra.Structures.IsMiddleBolLoop._.\\-congʳ
d_'92''92''45'cong'691'_3386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'691'_3386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'691'_3386 v8
du_'92''92''45'cong'691'_3386 ::
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'691'_3386 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'691'_2998 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.\\-congˡ
d_'92''92''45'cong'737'_3388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'737'_3388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'92''92''45'cong'737'_3388 v8
du_'92''92''45'cong'737'_3388 ::
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'737'_3388 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (coe
         du_'92''92''45'cong'737'_2994 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.identity
d_identity_3390 ::
  T_IsMiddleBolLoop_3358 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3390 v0
  = coe d_identity_3042 (coe d_isLoop_3372 (coe v0))
-- Algebra.Structures.IsMiddleBolLoop._.identityʳ
d_identity'691'_3392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny
d_identity'691'_3392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_3392 v8
du_identity'691'_3392 ::
  T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny
du_identity'691'_3392 v0
  = coe du_identity'691'_3094 (coe d_isLoop_3372 (coe v0))
-- Algebra.Structures.IsMiddleBolLoop._.identityˡ
d_identity'737'_3394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny
d_identity'737'_3394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_3394 v8
du_identity'737'_3394 ::
  T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny
du_identity'737'_3394 v0
  = coe du_identity'737'_3092 (coe d_isLoop_3372 (coe v0))
-- Algebra.Structures.IsMiddleBolLoop._.isEquivalence
d_isEquivalence_3396 ::
  T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_3396 v0
  = coe
      d_isEquivalence_184
      (coe
         d_isMagma_2962
         (coe d_isQuasigroup_3040 (coe d_isLoop_3372 (coe v0))))
-- Algebra.Structures.IsMiddleBolLoop._.isMagma
d_isMagma_3398 :: T_IsMiddleBolLoop_3358 -> T_IsMagma_176
d_isMagma_3398 v0
  = coe
      d_isMagma_2962
      (coe d_isQuasigroup_3040 (coe d_isLoop_3372 (coe v0)))
-- Algebra.Structures.IsMiddleBolLoop._.isPartialEquivalence
d_isPartialEquivalence_3400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_3400 v8
du_isPartialEquivalence_3400 ::
  T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3400 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe
         (let v3 = d_isMagma_2962 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.IsMiddleBolLoop._.isQuasigroup
d_isQuasigroup_3402 ::
  T_IsMiddleBolLoop_3358 -> T_IsQuasigroup_2944
d_isQuasigroup_3402 v0
  = coe d_isQuasigroup_3040 (coe d_isLoop_3372 (coe v0))
-- Algebra.Structures.IsMiddleBolLoop._.leftDivides
d_leftDivides_3404 ::
  T_IsMiddleBolLoop_3358 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_3404 v0
  = coe
      d_leftDivides_2968
      (coe d_isQuasigroup_3040 (coe d_isLoop_3372 (coe v0)))
-- Algebra.Structures.IsMiddleBolLoop._.leftDividesʳ
d_leftDivides'691'_3406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'691'_3406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'691'_3406 v8
du_leftDivides'691'_3406 ::
  T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'691'_3406 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (coe du_leftDivides'691'_3012 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.leftDividesˡ
d_leftDivides'737'_3408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny -> AgdaAny
d_leftDivides'737'_3408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_leftDivides'737'_3408 v8
du_leftDivides'737'_3408 ::
  T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny -> AgdaAny
du_leftDivides'737'_3408 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (coe du_leftDivides'737'_3010 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.refl
d_refl_3410 :: T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny
d_refl_3410 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe d_isQuasigroup_3040 (coe d_isLoop_3372 (coe v0)))))
-- Algebra.Structures.IsMiddleBolLoop._.reflexive
d_reflexive_3412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3412 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_3412 v8
du_reflexive_3412 ::
  T_IsMiddleBolLoop_3358 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3412 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe
         (let v3 = d_isMagma_2962 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_184 (coe v3)) v4)))
-- Algebra.Structures.IsMiddleBolLoop._.rightDivides
d_rightDivides_3414 ::
  T_IsMiddleBolLoop_3358 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_3414 v0
  = coe
      d_rightDivides_2970
      (coe d_isQuasigroup_3040 (coe d_isLoop_3372 (coe v0)))
-- Algebra.Structures.IsMiddleBolLoop._.rightDividesʳ
d_rightDivides'691'_3416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'691'_3416 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'691'_3416 v8
du_rightDivides'691'_3416 ::
  T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'691'_3416 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (coe du_rightDivides'691'_3016 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.rightDividesˡ
d_rightDivides'737'_3418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny -> AgdaAny
d_rightDivides'737'_3418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_rightDivides'737'_3418 v8
du_rightDivides'737'_3418 ::
  T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny -> AgdaAny
du_rightDivides'737'_3418 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (coe du_rightDivides'737'_3014 (coe d_isQuasigroup_3040 (coe v1)))
-- Algebra.Structures.IsMiddleBolLoop._.setoid
d_setoid_3420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_3420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_3420 v8
du_setoid_3420 ::
  T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_3420 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe (coe du_setoid_200 (coe d_isMagma_2962 (coe v2))))
-- Algebra.Structures.IsMiddleBolLoop._.sym
d_sym_3422 ::
  T_IsMiddleBolLoop_3358 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3422 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe d_isQuasigroup_3040 (coe d_isLoop_3372 (coe v0)))))
-- Algebra.Structures.IsMiddleBolLoop._.trans
d_trans_3424 ::
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3424 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_isEquivalence_184
         (coe
            d_isMagma_2962
            (coe d_isQuasigroup_3040 (coe d_isLoop_3372 (coe v0)))))
-- Algebra.Structures.IsMiddleBolLoop._.∙-cong
d_'8729''45'cong_3426 ::
  T_IsMiddleBolLoop_3358 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3426 v0
  = coe
      d_'8729''45'cong_186
      (coe
         d_isMagma_2962
         (coe d_isQuasigroup_3040 (coe d_isLoop_3372 (coe v0))))
-- Algebra.Structures.IsMiddleBolLoop._.∙-congʳ
d_'8729''45'cong'691'_3428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_3428 v8
du_'8729''45'cong'691'_3428 ::
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3428 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe (coe du_'8729''45'cong'691'_206 (coe d_isMagma_2962 (coe v2))))
-- Algebra.Structures.IsMiddleBolLoop._.∙-congˡ
d_'8729''45'cong'737'_3430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3430 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_3430 v8
du_'8729''45'cong'737'_3430 ::
  T_IsMiddleBolLoop_3358 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3430 v0
  = let v1 = d_isLoop_3372 (coe v0) in
    coe
      (let v2 = d_isQuasigroup_3040 (coe v1) in
       coe (coe du_'8729''45'cong'737'_202 (coe d_isMagma_2962 (coe v2))))
