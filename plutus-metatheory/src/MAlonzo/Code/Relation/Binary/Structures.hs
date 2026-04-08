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

module MAlonzo.Code.Relation.Binary.Structures where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.Structures.IsPartialEquivalence
d_IsPartialEquivalence_16 a0 a1 a2 a3 = ()
data T_IsPartialEquivalence_16
  = C_constructor_26 (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Structures.IsPartialEquivalence.sym
d_sym_22 ::
  T_IsPartialEquivalence_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_22 v0
  = case coe v0 of
      C_constructor_26 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPartialEquivalence.trans
d_trans_24 ::
  T_IsPartialEquivalence_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_24 v0
  = case coe v0 of
      C_constructor_26 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsEquivalence
d_IsEquivalence_28 a0 a1 a2 a3 = ()
data T_IsEquivalence_28
  = C_constructor_46 (AgdaAny -> AgdaAny)
                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Structures.IsEquivalence.refl
d_refl_36 :: T_IsEquivalence_28 -> AgdaAny -> AgdaAny
d_refl_36 v0
  = case coe v0 of
      C_constructor_46 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsEquivalence.sym
d_sym_38 ::
  T_IsEquivalence_28 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_38 v0
  = case coe v0 of
      C_constructor_46 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsEquivalence.trans
d_trans_40 ::
  T_IsEquivalence_28 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_40 v0
  = case coe v0 of
      C_constructor_46 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsEquivalence.reflexive
d_reflexive_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsEquivalence_28 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_42 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_reflexive_42 v4 v5
du_reflexive_42 :: T_IsEquivalence_28 -> AgdaAny -> AgdaAny
du_reflexive_42 v0 v1 = coe d_refl_36 v0 v1
-- Relation.Binary.Structures.IsEquivalence.isPartialEquivalence
d_isPartialEquivalence_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsEquivalence_28 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_44 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_44 v4
du_isPartialEquivalence_44 ::
  T_IsEquivalence_28 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_44 v0
  = coe
      C_constructor_26 (coe d_sym_38 (coe v0)) (coe d_trans_40 (coe v0))
-- Relation.Binary.Structures.IsDecEquivalence
d_IsDecEquivalence_48 a0 a1 a2 a3 = ()
data T_IsDecEquivalence_48
  = C_constructor_70 T_IsEquivalence_28
                     (AgdaAny ->
                      AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
-- Relation.Binary.Structures.IsDecEquivalence.isEquivalence
d_isEquivalence_54 :: T_IsDecEquivalence_48 -> T_IsEquivalence_28
d_isEquivalence_54 v0
  = case coe v0 of
      C_constructor_70 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecEquivalence._≟_
d__'8799'__56 ::
  T_IsDecEquivalence_48 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__56 v0
  = case coe v0 of
      C_constructor_70 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecEquivalence._.isPartialEquivalence
d_isPartialEquivalence_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecEquivalence_48 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_60 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_60 v4
du_isPartialEquivalence_60 ::
  T_IsDecEquivalence_48 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_60 v0
  = coe du_isPartialEquivalence_44 (coe d_isEquivalence_54 (coe v0))
-- Relation.Binary.Structures.IsDecEquivalence._.refl
d_refl_62 :: T_IsDecEquivalence_48 -> AgdaAny -> AgdaAny
d_refl_62 v0 = coe d_refl_36 (coe d_isEquivalence_54 (coe v0))
-- Relation.Binary.Structures.IsDecEquivalence._.reflexive
d_reflexive_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecEquivalence_48 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_64 ~v0 ~v1 ~v2 ~v3 v4 = du_reflexive_64 v4
du_reflexive_64 ::
  T_IsDecEquivalence_48 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_64 v0 v1 v2 v3
  = coe du_reflexive_42 (coe d_isEquivalence_54 (coe v0)) v1
-- Relation.Binary.Structures.IsDecEquivalence._.sym
d_sym_66 ::
  T_IsDecEquivalence_48 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_66 v0 = coe d_sym_38 (coe d_isEquivalence_54 (coe v0))
-- Relation.Binary.Structures.IsDecEquivalence._.trans
d_trans_68 ::
  T_IsDecEquivalence_48 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_68 v0 = coe d_trans_40 (coe d_isEquivalence_54 (coe v0))
-- Relation.Binary.Structures.IsPreorder
d_IsPreorder_76 a0 a1 a2 a3 a4 a5 = ()
data T_IsPreorder_76
  = C_constructor_126 T_IsEquivalence_28
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Structures.IsPreorder.isEquivalence
d_isEquivalence_86 :: T_IsPreorder_76 -> T_IsEquivalence_28
d_isEquivalence_86 v0
  = case coe v0 of
      C_constructor_126 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPreorder.reflexive
d_reflexive_88 ::
  T_IsPreorder_76 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_88 v0
  = case coe v0 of
      C_constructor_126 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPreorder.trans
d_trans_90 ::
  T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_90 v0
  = case coe v0 of
      C_constructor_126 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPreorder.Eq.isPartialEquivalence
d_isPartialEquivalence_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_76 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_94 v6
du_isPartialEquivalence_94 ::
  T_IsPreorder_76 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_94 v0
  = coe du_isPartialEquivalence_44 (coe d_isEquivalence_86 (coe v0))
-- Relation.Binary.Structures.IsPreorder.Eq.refl
d_refl_96 :: T_IsPreorder_76 -> AgdaAny -> AgdaAny
d_refl_96 v0 = coe d_refl_36 (coe d_isEquivalence_86 (coe v0))
-- Relation.Binary.Structures.IsPreorder.Eq.reflexive
d_reflexive_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_98 v6
du_reflexive_98 ::
  T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_98 v0 v1 v2 v3
  = coe du_reflexive_42 (coe d_isEquivalence_86 (coe v0)) v1
-- Relation.Binary.Structures.IsPreorder.Eq.sym
d_sym_100 ::
  T_IsPreorder_76 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_100 v0 = coe d_sym_38 (coe d_isEquivalence_86 (coe v0))
-- Relation.Binary.Structures.IsPreorder.Eq.trans
d_trans_102 ::
  T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_102 v0 = coe d_trans_40 (coe d_isEquivalence_86 (coe v0))
-- Relation.Binary.Structures.IsPreorder.refl
d_refl_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> T_IsPreorder_76 -> AgdaAny -> AgdaAny
d_refl_104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_refl_104 v6 v7
du_refl_104 :: T_IsPreorder_76 -> AgdaAny -> AgdaAny
du_refl_104 v0 v1
  = coe
      d_reflexive_88 v0 v1 v1
      (coe d_refl_36 (d_isEquivalence_86 (coe v0)) v1)
-- Relation.Binary.Structures.IsPreorder.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                    v8 v9 v10 v11
  = du_'8818''45'resp'737''45''8776'_106 v6 v7 v8 v9 v10 v11
du_'8818''45'resp'737''45''8776'_106 ::
  T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_106 v0 v1 v2 v3 v4 v5
  = coe
      d_trans_90 v0 v3 v2 v1
      (coe
         d_reflexive_88 v0 v3 v2
         (coe d_sym_38 (d_isEquivalence_86 (coe v0)) v2 v3 v4))
      v5
-- Relation.Binary.Structures.IsPreorder.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                    v8 v9 v10 v11
  = du_'8818''45'resp'691''45''8776'_112 v6 v7 v8 v9 v10 v11
du_'8818''45'resp'691''45''8776'_112 ::
  T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_112 v0 v1 v2 v3 v4 v5
  = coe d_trans_90 v0 v1 v2 v3 v5 (coe d_reflexive_88 v0 v2 v3 v4)
-- Relation.Binary.Structures.IsPreorder.≲-resp-≈
d_'8818''45'resp'45''8776'_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_76 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_118 v6
du_'8818''45'resp'45''8776'_118 ::
  T_IsPreorder_76 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_118 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8818''45'resp'691''45''8776'_112 (coe v0))
      (coe du_'8818''45'resp'737''45''8776'_106 (coe v0))
-- Relation.Binary.Structures.IsPreorder.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_120 v6
du_'8764''45'resp'737''45''8776'_120 ::
  T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_120 v0
  = coe du_'8818''45'resp'737''45''8776'_106 (coe v0)
-- Relation.Binary.Structures.IsPreorder.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_122 v6
du_'8764''45'resp'691''45''8776'_122 ::
  T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_122 v0
  = coe du_'8818''45'resp'691''45''8776'_112 (coe v0)
-- Relation.Binary.Structures.IsPreorder.∼-resp-≈
d_'8764''45'resp'45''8776'_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_76 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_124 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_124 v6
du_'8764''45'resp'45''8776'_124 ::
  T_IsPreorder_76 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_124 v0
  = coe du_'8818''45'resp'45''8776'_118 (coe v0)
-- Relation.Binary.Structures.IsTotalPreorder
d_IsTotalPreorder_132 a0 a1 a2 a3 a4 a5 = ()
data T_IsTotalPreorder_132
  = C_constructor_178 T_IsPreorder_76
                      (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Relation.Binary.Structures.IsTotalPreorder.isPreorder
d_isPreorder_140 :: T_IsTotalPreorder_132 -> T_IsPreorder_76
d_isPreorder_140 v0
  = case coe v0 of
      C_constructor_178 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsTotalPreorder.total
d_total_142 ::
  T_IsTotalPreorder_132 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_142 v0
  = case coe v0 of
      C_constructor_178 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsTotalPreorder._.isEquivalence
d_isEquivalence_146 :: T_IsTotalPreorder_132 -> T_IsEquivalence_28
d_isEquivalence_146 v0
  = coe d_isEquivalence_86 (coe d_isPreorder_140 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.refl
d_refl_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_132 -> AgdaAny -> AgdaAny
d_refl_148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_148 v6
du_refl_148 :: T_IsTotalPreorder_132 -> AgdaAny -> AgdaAny
du_refl_148 v0 = coe du_refl_104 (coe d_isPreorder_140 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.reflexive
d_reflexive_150 ::
  T_IsTotalPreorder_132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_150 v0
  = coe d_reflexive_88 (coe d_isPreorder_140 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.trans
d_trans_152 ::
  T_IsTotalPreorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_152 v0 = coe d_trans_90 (coe d_isPreorder_140 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.∼-resp-≈
d_'8764''45'resp'45''8776'_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_132 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_154 v6
du_'8764''45'resp'45''8776'_154 ::
  T_IsTotalPreorder_132 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_154 v0
  = coe
      du_'8764''45'resp'45''8776'_124 (coe d_isPreorder_140 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_156 v6
du_'8764''45'resp'691''45''8776'_156 ::
  T_IsTotalPreorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_156 v0
  = coe
      du_'8764''45'resp'691''45''8776'_122
      (coe d_isPreorder_140 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_158 v6
du_'8764''45'resp'737''45''8776'_158 ::
  T_IsTotalPreorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_158 v0
  = coe
      du_'8764''45'resp'737''45''8776'_120
      (coe d_isPreorder_140 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.≲-resp-≈
d_'8818''45'resp'45''8776'_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_132 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_160 v6
du_'8818''45'resp'45''8776'_160 ::
  T_IsTotalPreorder_132 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_160 v0
  = coe
      du_'8818''45'resp'45''8776'_118 (coe d_isPreorder_140 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'691''45''8776'_162 v6
du_'8818''45'resp'691''45''8776'_162 ::
  T_IsTotalPreorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_162 v0
  = coe
      du_'8818''45'resp'691''45''8776'_112
      (coe d_isPreorder_140 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'737''45''8776'_164 v6
du_'8818''45'resp'737''45''8776'_164 ::
  T_IsTotalPreorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_164 v0
  = coe
      du_'8818''45'resp'737''45''8776'_106
      (coe d_isPreorder_140 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.Eq.isPartialEquivalence
d_isPartialEquivalence_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_132 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_168 v6
du_isPartialEquivalence_168 ::
  T_IsTotalPreorder_132 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_168 v0
  = let v1 = d_isPreorder_140 (coe v0) in
    coe
      (coe du_isPartialEquivalence_44 (coe d_isEquivalence_86 (coe v1)))
-- Relation.Binary.Structures.IsTotalPreorder._.Eq.refl
d_refl_170 :: T_IsTotalPreorder_132 -> AgdaAny -> AgdaAny
d_refl_170 v0
  = coe
      d_refl_36 (coe d_isEquivalence_86 (coe d_isPreorder_140 (coe v0)))
-- Relation.Binary.Structures.IsTotalPreorder._.Eq.reflexive
d_reflexive_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_172 v6
du_reflexive_172 ::
  T_IsTotalPreorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_172 v0
  = let v1 = d_isPreorder_140 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_42 (coe d_isEquivalence_86 (coe v1)) v2)
-- Relation.Binary.Structures.IsTotalPreorder._.Eq.sym
d_sym_174 ::
  T_IsTotalPreorder_132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_174 v0
  = coe
      d_sym_38 (coe d_isEquivalence_86 (coe d_isPreorder_140 (coe v0)))
-- Relation.Binary.Structures.IsTotalPreorder._.Eq.trans
d_trans_176 ::
  T_IsTotalPreorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_176 v0
  = coe
      d_trans_40 (coe d_isEquivalence_86 (coe d_isPreorder_140 (coe v0)))
-- Relation.Binary.Structures.IsDecPreorder
d_IsDecPreorder_184 a0 a1 a2 a3 a4 a5 = ()
data T_IsDecPreorder_184
  = C_constructor_242 T_IsPreorder_76
                      (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                      (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
-- Relation.Binary.Structures.IsDecPreorder.isPreorder
d_isPreorder_194 :: T_IsDecPreorder_184 -> T_IsPreorder_76
d_isPreorder_194 v0
  = case coe v0 of
      C_constructor_242 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecPreorder._≟_
d__'8799'__196 ::
  T_IsDecPreorder_184 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__196 v0
  = case coe v0 of
      C_constructor_242 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecPreorder._≲?_
d__'8818''63'__198 ::
  T_IsDecPreorder_184 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8818''63'__198 v0
  = case coe v0 of
      C_constructor_242 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecPreorder._.isEquivalence
d_isEquivalence_202 :: T_IsDecPreorder_184 -> T_IsEquivalence_28
d_isEquivalence_202 v0
  = coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder._.refl
d_refl_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 -> AgdaAny -> AgdaAny
d_refl_204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_204 v6
du_refl_204 :: T_IsDecPreorder_184 -> AgdaAny -> AgdaAny
du_refl_204 v0 = coe du_refl_104 (coe d_isPreorder_194 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder._.reflexive
d_reflexive_206 ::
  T_IsDecPreorder_184 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_206 v0
  = coe d_reflexive_88 (coe d_isPreorder_194 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder._.trans
d_trans_208 ::
  T_IsDecPreorder_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_208 v0 = coe d_trans_90 (coe d_isPreorder_194 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder._.∼-resp-≈
d_'8764''45'resp'45''8776'_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_210 v6
du_'8764''45'resp'45''8776'_210 ::
  T_IsDecPreorder_184 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_210 v0
  = coe
      du_'8764''45'resp'45''8776'_124 (coe d_isPreorder_194 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_212 v6
du_'8764''45'resp'691''45''8776'_212 ::
  T_IsDecPreorder_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_212 v0
  = coe
      du_'8764''45'resp'691''45''8776'_122
      (coe d_isPreorder_194 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_214 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_214 v6
du_'8764''45'resp'737''45''8776'_214 ::
  T_IsDecPreorder_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_214 v0
  = coe
      du_'8764''45'resp'737''45''8776'_120
      (coe d_isPreorder_194 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder._.≲-resp-≈
d_'8818''45'resp'45''8776'_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_216 v6
du_'8818''45'resp'45''8776'_216 ::
  T_IsDecPreorder_184 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_216 v0
  = coe
      du_'8818''45'resp'45''8776'_118 (coe d_isPreorder_194 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'691''45''8776'_218 v6
du_'8818''45'resp'691''45''8776'_218 ::
  T_IsDecPreorder_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_218 v0
  = coe
      du_'8818''45'resp'691''45''8776'_112
      (coe d_isPreorder_194 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'737''45''8776'_220 v6
du_'8818''45'resp'737''45''8776'_220 ::
  T_IsDecPreorder_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_220 v0
  = coe
      du_'8818''45'resp'737''45''8776'_106
      (coe d_isPreorder_194 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder.Eq.isDecEquivalence
d_isDecEquivalence_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 -> T_IsDecEquivalence_48
d_isDecEquivalence_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_224 v6
du_isDecEquivalence_224 ::
  T_IsDecPreorder_184 -> T_IsDecEquivalence_48
du_isDecEquivalence_224 v0
  = coe
      C_constructor_70
      (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v0)))
      (coe d__'8799'__196 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder.Eq._._≟_
d__'8799'__228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__228 v6
du__'8799'__228 ::
  T_IsDecPreorder_184 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__228 v0 = coe d__'8799'__196 (coe v0)
-- Relation.Binary.Structures.IsDecPreorder.Eq._.isEquivalence
d_isEquivalence_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 -> T_IsEquivalence_28
d_isEquivalence_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_230 v6
du_isEquivalence_230 :: T_IsDecPreorder_184 -> T_IsEquivalence_28
du_isEquivalence_230 v0
  = coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v0))
-- Relation.Binary.Structures.IsDecPreorder.Eq._.isPartialEquivalence
d_isPartialEquivalence_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_232 v6
du_isPartialEquivalence_232 ::
  T_IsDecPreorder_184 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_232 v0
  = let v1 = coe du_isDecEquivalence_224 (coe v0) in
    coe
      (coe du_isPartialEquivalence_44 (coe d_isEquivalence_54 (coe v1)))
-- Relation.Binary.Structures.IsDecPreorder.Eq._.refl
d_refl_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 -> AgdaAny -> AgdaAny
d_refl_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_234 v6
du_refl_234 :: T_IsDecPreorder_184 -> AgdaAny -> AgdaAny
du_refl_234 v0
  = coe
      d_refl_36 (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v0)))
-- Relation.Binary.Structures.IsDecPreorder.Eq._.reflexive
d_reflexive_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_236 v6
du_reflexive_236 ::
  T_IsDecPreorder_184 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_236 v0
  = let v1 = coe du_isDecEquivalence_224 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_42 (coe d_isEquivalence_54 (coe v1)) v2)
-- Relation.Binary.Structures.IsDecPreorder.Eq._.sym
d_sym_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_238 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_238 v6
du_sym_238 ::
  T_IsDecPreorder_184 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_238 v0
  = coe
      d_sym_38 (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v0)))
-- Relation.Binary.Structures.IsDecPreorder.Eq._.trans
d_trans_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPreorder_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_240 v6
du_trans_240 ::
  T_IsDecPreorder_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_240 v0
  = coe
      d_trans_40 (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v0)))
-- Relation.Binary.Structures.IsPartialOrder
d_IsPartialOrder_248 a0 a1 a2 a3 a4 a5 = ()
data T_IsPartialOrder_248
  = C_constructor_294 T_IsPreorder_76
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Structures.IsPartialOrder.isPreorder
d_isPreorder_256 :: T_IsPartialOrder_248 -> T_IsPreorder_76
d_isPreorder_256 v0
  = case coe v0 of
      C_constructor_294 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPartialOrder.antisym
d_antisym_258 ::
  T_IsPartialOrder_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_258 v0
  = case coe v0 of
      C_constructor_294 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPartialOrder._.isEquivalence
d_isEquivalence_262 :: T_IsPartialOrder_248 -> T_IsEquivalence_28
d_isEquivalence_262 v0
  = coe d_isEquivalence_86 (coe d_isPreorder_256 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.refl
d_refl_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_248 -> AgdaAny -> AgdaAny
d_refl_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_264 v6
du_refl_264 :: T_IsPartialOrder_248 -> AgdaAny -> AgdaAny
du_refl_264 v0 = coe du_refl_104 (coe d_isPreorder_256 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.reflexive
d_reflexive_266 ::
  T_IsPartialOrder_248 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_266 v0
  = coe d_reflexive_88 (coe d_isPreorder_256 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.trans
d_trans_268 ::
  T_IsPartialOrder_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_268 v0 = coe d_trans_90 (coe d_isPreorder_256 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_248 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_270 v6
du_'8764''45'resp'45''8776'_270 ::
  T_IsPartialOrder_248 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_270 v0
  = coe
      du_'8764''45'resp'45''8776'_124 (coe d_isPreorder_256 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_272 v6
du_'8764''45'resp'691''45''8776'_272 ::
  T_IsPartialOrder_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_272 v0
  = coe
      du_'8764''45'resp'691''45''8776'_122
      (coe d_isPreorder_256 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_274 v6
du_'8764''45'resp'737''45''8776'_274 ::
  T_IsPartialOrder_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_274 v0
  = coe
      du_'8764''45'resp'737''45''8776'_120
      (coe d_isPreorder_256 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_248 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_276 v6
du_'8818''45'resp'45''8776'_276 ::
  T_IsPartialOrder_248 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_276 v0
  = coe
      du_'8818''45'resp'45''8776'_118 (coe d_isPreorder_256 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'691''45''8776'_278 v6
du_'8818''45'resp'691''45''8776'_278 ::
  T_IsPartialOrder_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_278 v0
  = coe
      du_'8818''45'resp'691''45''8776'_112
      (coe d_isPreorder_256 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'737''45''8776'_280 v6
du_'8818''45'resp'737''45''8776'_280 ::
  T_IsPartialOrder_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_280 v0
  = coe
      du_'8818''45'resp'737''45''8776'_106
      (coe d_isPreorder_256 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_248 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_284 v6
du_isPartialEquivalence_284 ::
  T_IsPartialOrder_248 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_284 v0
  = let v1 = d_isPreorder_256 (coe v0) in
    coe
      (coe du_isPartialEquivalence_44 (coe d_isEquivalence_86 (coe v1)))
-- Relation.Binary.Structures.IsPartialOrder._.Eq.refl
d_refl_286 :: T_IsPartialOrder_248 -> AgdaAny -> AgdaAny
d_refl_286 v0
  = coe
      d_refl_36 (coe d_isEquivalence_86 (coe d_isPreorder_256 (coe v0)))
-- Relation.Binary.Structures.IsPartialOrder._.Eq.reflexive
d_reflexive_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_248 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_288 v6
du_reflexive_288 ::
  T_IsPartialOrder_248 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_288 v0
  = let v1 = d_isPreorder_256 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_42 (coe d_isEquivalence_86 (coe v1)) v2)
-- Relation.Binary.Structures.IsPartialOrder._.Eq.sym
d_sym_290 ::
  T_IsPartialOrder_248 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_290 v0
  = coe
      d_sym_38 (coe d_isEquivalence_86 (coe d_isPreorder_256 (coe v0)))
-- Relation.Binary.Structures.IsPartialOrder._.Eq.trans
d_trans_292 ::
  T_IsPartialOrder_248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_292 v0
  = coe
      d_trans_40 (coe d_isEquivalence_86 (coe d_isPreorder_256 (coe v0)))
-- Relation.Binary.Structures.IsDecPartialOrder
d_IsDecPartialOrder_300 a0 a1 a2 a3 a4 a5 = ()
data T_IsDecPartialOrder_300
  = C_constructor_364 T_IsPartialOrder_248
                      (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                      (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
-- Relation.Binary.Structures.IsDecPartialOrder.isPartialOrder
d_isPartialOrder_310 ::
  T_IsDecPartialOrder_300 -> T_IsPartialOrder_248
d_isPartialOrder_310 v0
  = case coe v0 of
      C_constructor_364 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecPartialOrder._≟_
d__'8799'__312 ::
  T_IsDecPartialOrder_300 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__312 v0
  = case coe v0 of
      C_constructor_364 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecPartialOrder._≤?_
d__'8804''63'__314 ::
  T_IsDecPartialOrder_300 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__314 v0
  = case coe v0 of
      C_constructor_364 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecPartialOrder._.antisym
d_antisym_318 ::
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_318 v0
  = coe d_antisym_258 (coe d_isPartialOrder_310 (coe v0))
-- Relation.Binary.Structures.IsDecPartialOrder._.isEquivalence
d_isEquivalence_320 ::
  T_IsDecPartialOrder_300 -> T_IsEquivalence_28
d_isEquivalence_320 v0
  = coe
      d_isEquivalence_86
      (coe d_isPreorder_256 (coe d_isPartialOrder_310 (coe v0)))
-- Relation.Binary.Structures.IsDecPartialOrder._.isPreorder
d_isPreorder_322 :: T_IsDecPartialOrder_300 -> T_IsPreorder_76
d_isPreorder_322 v0
  = coe d_isPreorder_256 (coe d_isPartialOrder_310 (coe v0))
-- Relation.Binary.Structures.IsDecPartialOrder._.refl
d_refl_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 -> AgdaAny -> AgdaAny
d_refl_324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_324 v6
du_refl_324 :: T_IsDecPartialOrder_300 -> AgdaAny -> AgdaAny
du_refl_324 v0
  = let v1 = d_isPartialOrder_310 (coe v0) in
    coe (coe du_refl_104 (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.reflexive
d_reflexive_326 ::
  T_IsDecPartialOrder_300 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_326 v0
  = coe
      d_reflexive_88
      (coe d_isPreorder_256 (coe d_isPartialOrder_310 (coe v0)))
-- Relation.Binary.Structures.IsDecPartialOrder._.trans
d_trans_328 ::
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_328 v0
  = coe
      d_trans_90
      (coe d_isPreorder_256 (coe d_isPartialOrder_310 (coe v0)))
-- Relation.Binary.Structures.IsDecPartialOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_330 v6
du_'8764''45'resp'45''8776'_330 ::
  T_IsDecPartialOrder_300 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_330 v0
  = let v1 = d_isPartialOrder_310 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'45''8776'_124 (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_332 v6
du_'8764''45'resp'691''45''8776'_332 ::
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_332 v0
  = let v1 = d_isPartialOrder_310 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'691''45''8776'_122
         (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_334 v6
du_'8764''45'resp'737''45''8776'_334 ::
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_334 v0
  = let v1 = d_isPartialOrder_310 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'737''45''8776'_120
         (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_336 v6
du_'8818''45'resp'45''8776'_336 ::
  T_IsDecPartialOrder_300 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_336 v0
  = let v1 = d_isPartialOrder_310 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'45''8776'_118 (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'691''45''8776'_338 v6
du_'8818''45'resp'691''45''8776'_338 ::
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_338 v0
  = let v1 = d_isPartialOrder_310 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'691''45''8776'_112
         (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'737''45''8776'_340 v6
du_'8818''45'resp'737''45''8776'_340 ::
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_340 v0
  = let v1 = d_isPartialOrder_310 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'737''45''8776'_106
         (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder.isDecPreorder
d_isDecPreorder_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 -> T_IsDecPreorder_184
d_isDecPreorder_342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecPreorder_342 v6
du_isDecPreorder_342 ::
  T_IsDecPartialOrder_300 -> T_IsDecPreorder_184
du_isDecPreorder_342 v0
  = coe
      C_constructor_242
      (coe d_isPreorder_256 (coe d_isPartialOrder_310 (coe v0)))
      (coe d__'8799'__312 (coe v0)) (coe d__'8804''63'__314 (coe v0))
-- Relation.Binary.Structures.IsDecPartialOrder._.Eq._≟_
d__'8799'__348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__348 v6
du__'8799'__348 ::
  T_IsDecPartialOrder_300 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__348 v0
  = let v1 = coe du_isDecPreorder_342 (coe v0) in
    coe (coe d__'8799'__196 (coe v1))
-- Relation.Binary.Structures.IsDecPartialOrder._.Eq.isDecEquivalence
d_isDecEquivalence_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 -> T_IsDecEquivalence_48
d_isDecEquivalence_350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_350 v6
du_isDecEquivalence_350 ::
  T_IsDecPartialOrder_300 -> T_IsDecEquivalence_48
du_isDecEquivalence_350 v0
  = coe du_isDecEquivalence_224 (coe du_isDecPreorder_342 (coe v0))
-- Relation.Binary.Structures.IsDecPartialOrder._.Eq.isEquivalence
d_isEquivalence_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 -> T_IsEquivalence_28
d_isEquivalence_352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_352 v6
du_isEquivalence_352 ::
  T_IsDecPartialOrder_300 -> T_IsEquivalence_28
du_isEquivalence_352 v0
  = let v1 = coe du_isDecPreorder_342 (coe v0) in
    coe (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_354 v6
du_isPartialEquivalence_354 ::
  T_IsDecPartialOrder_300 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_354 v0
  = let v1 = coe du_isDecPreorder_342 (coe v0) in
    coe
      (let v2 = coe du_isDecEquivalence_224 (coe v1) in
       coe
         (coe du_isPartialEquivalence_44 (coe d_isEquivalence_54 (coe v2))))
-- Relation.Binary.Structures.IsDecPartialOrder._.Eq.refl
d_refl_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 -> AgdaAny -> AgdaAny
d_refl_356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_356 v6
du_refl_356 :: T_IsDecPartialOrder_300 -> AgdaAny -> AgdaAny
du_refl_356 v0
  = let v1 = coe du_isDecPreorder_342 (coe v0) in
    coe
      (coe
         d_refl_36 (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v1))))
-- Relation.Binary.Structures.IsDecPartialOrder._.Eq.reflexive
d_reflexive_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_358 v6
du_reflexive_358 ::
  T_IsDecPartialOrder_300 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_358 v0
  = let v1 = coe du_isDecPreorder_342 (coe v0) in
    coe
      (let v2 = coe du_isDecEquivalence_224 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe du_reflexive_42 (coe d_isEquivalence_54 (coe v2)) v3))
-- Relation.Binary.Structures.IsDecPartialOrder._.Eq.sym
d_sym_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_360 v6
du_sym_360 ::
  T_IsDecPartialOrder_300 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_360 v0
  = let v1 = coe du_isDecPreorder_342 (coe v0) in
    coe
      (coe
         d_sym_38 (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v1))))
-- Relation.Binary.Structures.IsDecPartialOrder._.Eq.trans
d_trans_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_362 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_362 v6
du_trans_362 ::
  T_IsDecPartialOrder_300 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_362 v0
  = let v1 = coe du_isDecPreorder_342 (coe v0) in
    coe
      (coe
         d_trans_40
         (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v1))))
-- Relation.Binary.Structures.IsStrictPartialOrder
d_IsStrictPartialOrder_370 a0 a1 a2 a3 a4 a5 = ()
data T_IsStrictPartialOrder_370
  = C_constructor_412 T_IsEquivalence_28
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Relation.Binary.Structures.IsStrictPartialOrder.isEquivalence
d_isEquivalence_382 ::
  T_IsStrictPartialOrder_370 -> T_IsEquivalence_28
d_isEquivalence_382 v0
  = case coe v0 of
      C_constructor_412 v1 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsStrictPartialOrder.irrefl
d_irrefl_384 ::
  T_IsStrictPartialOrder_370 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_384 = erased
-- Relation.Binary.Structures.IsStrictPartialOrder.trans
d_trans_386 ::
  T_IsStrictPartialOrder_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_386 v0
  = case coe v0 of
      C_constructor_412 v1 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsStrictPartialOrder.<-resp-≈
d_'60''45'resp'45''8776'_388 ::
  T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_388 v0
  = case coe v0 of
      C_constructor_412 v1 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsStrictPartialOrder.Eq.isPartialEquivalence
d_isPartialEquivalence_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictPartialOrder_370 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_392 v6
du_isPartialEquivalence_392 ::
  T_IsStrictPartialOrder_370 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_392 v0
  = coe du_isPartialEquivalence_44 (coe d_isEquivalence_382 (coe v0))
-- Relation.Binary.Structures.IsStrictPartialOrder.Eq.refl
d_refl_394 :: T_IsStrictPartialOrder_370 -> AgdaAny -> AgdaAny
d_refl_394 v0 = coe d_refl_36 (coe d_isEquivalence_382 (coe v0))
-- Relation.Binary.Structures.IsStrictPartialOrder.Eq.reflexive
d_reflexive_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictPartialOrder_370 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_396 v6
du_reflexive_396 ::
  T_IsStrictPartialOrder_370 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_396 v0 v1 v2 v3
  = coe du_reflexive_42 (coe d_isEquivalence_382 (coe v0)) v1
-- Relation.Binary.Structures.IsStrictPartialOrder.Eq.sym
d_sym_398 ::
  T_IsStrictPartialOrder_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_398 v0 = coe d_sym_38 (coe d_isEquivalence_382 (coe v0))
-- Relation.Binary.Structures.IsStrictPartialOrder.Eq.trans
d_trans_400 ::
  T_IsStrictPartialOrder_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_400 v0 = coe d_trans_40 (coe d_isEquivalence_382 (coe v0))
-- Relation.Binary.Structures.IsStrictPartialOrder.asym
d_asym_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictPartialOrder_370 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_402 = erased
-- Relation.Binary.Structures.IsStrictPartialOrder.<-respʳ-≈
d_'60''45'resp'691''45''8776'_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictPartialOrder_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
                                  v9
  = du_'60''45'resp'691''45''8776'_408 v6 v7 v8 v9
du_'60''45'resp'691''45''8776'_408 ::
  T_IsStrictPartialOrder_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_408 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (d_'60''45'resp'45''8776'_388 (coe v0)) v1 v2 v3
-- Relation.Binary.Structures.IsStrictPartialOrder.<-respˡ-≈
d_'60''45'resp'737''45''8776'_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictPartialOrder_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
                                  v9
  = du_'60''45'resp'737''45''8776'_410 v6 v7 v8 v9
du_'60''45'resp'737''45''8776'_410 ::
  T_IsStrictPartialOrder_370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_410 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (d_'60''45'resp'45''8776'_388 (coe v0)) v1 v2 v3
-- Relation.Binary.Structures.IsDecStrictPartialOrder
d_IsDecStrictPartialOrder_418 a0 a1 a2 a3 a4 a5 = ()
data T_IsDecStrictPartialOrder_418
  = C_constructor_482 T_IsStrictPartialOrder_370
                      (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                      (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
-- Relation.Binary.Structures.IsDecStrictPartialOrder.isStrictPartialOrder
d_isStrictPartialOrder_428 ::
  T_IsDecStrictPartialOrder_418 -> T_IsStrictPartialOrder_370
d_isStrictPartialOrder_428 v0
  = case coe v0 of
      C_constructor_482 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecStrictPartialOrder._≟_
d__'8799'__430 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__430 v0
  = case coe v0 of
      C_constructor_482 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecStrictPartialOrder._<?_
d__'60''63'__432 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__432 v0
  = case coe v0 of
      C_constructor_482 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.<-resp-≈
d_'60''45'resp'45''8776'_436 ::
  T_IsDecStrictPartialOrder_418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_436 v0
  = coe
      d_'60''45'resp'45''8776'_388
      (coe d_isStrictPartialOrder_428 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.<-respʳ-≈
d_'60''45'resp'691''45''8776'_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'691''45''8776'_438 v6
du_'60''45'resp'691''45''8776'_438 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_438 v0
  = coe
      du_'60''45'resp'691''45''8776'_408
      (coe d_isStrictPartialOrder_428 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.<-respˡ-≈
d_'60''45'resp'737''45''8776'_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'737''45''8776'_440 v6
du_'60''45'resp'737''45''8776'_440 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_440 v0
  = coe
      du_'60''45'resp'737''45''8776'_410
      (coe d_isStrictPartialOrder_428 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.asym
d_asym_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_442 = erased
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.irrefl
d_irrefl_444 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_444 = erased
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.isEquivalence
d_isEquivalence_446 ::
  T_IsDecStrictPartialOrder_418 -> T_IsEquivalence_28
d_isEquivalence_446 v0
  = coe d_isEquivalence_382 (coe d_isStrictPartialOrder_428 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.trans
d_trans_448 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_448 v0
  = coe d_trans_386 (coe d_isStrictPartialOrder_428 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.Eq.isPartialEquivalence
d_isPartialEquivalence_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_452 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_452 v6
du_isPartialEquivalence_452 ::
  T_IsDecStrictPartialOrder_418 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_452 v0
  = let v1 = d_isStrictPartialOrder_428 (coe v0) in
    coe
      (coe du_isPartialEquivalence_44 (coe d_isEquivalence_382 (coe v1)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.Eq.refl
d_refl_454 :: T_IsDecStrictPartialOrder_418 -> AgdaAny -> AgdaAny
d_refl_454 v0
  = coe
      d_refl_36
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_428 (coe v0)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.Eq.reflexive
d_reflexive_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_456 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_456 v6
du_reflexive_456 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_456 v0
  = let v1 = d_isStrictPartialOrder_428 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_42 (coe d_isEquivalence_382 (coe v1)) v2)
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.Eq.sym
d_sym_458 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_458 v0
  = coe
      d_sym_38
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_428 (coe v0)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.Eq.trans
d_trans_460 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_460 v0
  = coe
      d_trans_40
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_428 (coe v0)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq.isDecEquivalence
d_isDecEquivalence_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 -> T_IsDecEquivalence_48
d_isDecEquivalence_464 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_464 v6
du_isDecEquivalence_464 ::
  T_IsDecStrictPartialOrder_418 -> T_IsDecEquivalence_48
du_isDecEquivalence_464 v0
  = coe
      C_constructor_70
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_428 (coe v0)))
      (coe d__'8799'__430 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._._≟_
d__'8799'__468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__468 v6
du__'8799'__468 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__468 v0 = coe d__'8799'__430 (coe v0)
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.isEquivalence
d_isEquivalence_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 -> T_IsEquivalence_28
d_isEquivalence_470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_470 v6
du_isEquivalence_470 ::
  T_IsDecStrictPartialOrder_418 -> T_IsEquivalence_28
du_isEquivalence_470 v0
  = coe d_isEquivalence_382 (coe d_isStrictPartialOrder_428 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.isPartialEquivalence
d_isPartialEquivalence_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_472 v6
du_isPartialEquivalence_472 ::
  T_IsDecStrictPartialOrder_418 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_472 v0
  = let v1 = coe du_isDecEquivalence_464 (coe v0) in
    coe
      (coe du_isPartialEquivalence_44 (coe d_isEquivalence_54 (coe v1)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.refl
d_refl_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 -> AgdaAny -> AgdaAny
d_refl_474 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_474 v6
du_refl_474 :: T_IsDecStrictPartialOrder_418 -> AgdaAny -> AgdaAny
du_refl_474 v0
  = coe
      d_refl_36
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_428 (coe v0)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.reflexive
d_reflexive_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_476 v6
du_reflexive_476 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_476 v0
  = let v1 = coe du_isDecEquivalence_464 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_42 (coe d_isEquivalence_54 (coe v1)) v2)
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.sym
d_sym_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_478 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_478 v6
du_sym_478 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_478 v0
  = coe
      d_sym_38
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_428 (coe v0)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.trans
d_trans_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_480 v6
du_trans_480 ::
  T_IsDecStrictPartialOrder_418 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_480 v0
  = coe
      d_trans_40
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_428 (coe v0)))
-- Relation.Binary.Structures.IsTotalOrder
d_IsTotalOrder_488 a0 a1 a2 a3 a4 a5 = ()
data T_IsTotalOrder_488
  = C_constructor_540 T_IsPartialOrder_248
                      (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Relation.Binary.Structures.IsTotalOrder.isPartialOrder
d_isPartialOrder_496 :: T_IsTotalOrder_488 -> T_IsPartialOrder_248
d_isPartialOrder_496 v0
  = case coe v0 of
      C_constructor_540 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsTotalOrder.total
d_total_498 ::
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_498 v0
  = case coe v0 of
      C_constructor_540 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsTotalOrder._.antisym
d_antisym_502 ::
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_502 v0
  = coe d_antisym_258 (coe d_isPartialOrder_496 (coe v0))
-- Relation.Binary.Structures.IsTotalOrder._.isEquivalence
d_isEquivalence_504 :: T_IsTotalOrder_488 -> T_IsEquivalence_28
d_isEquivalence_504 v0
  = coe
      d_isEquivalence_86
      (coe d_isPreorder_256 (coe d_isPartialOrder_496 (coe v0)))
-- Relation.Binary.Structures.IsTotalOrder._.isPreorder
d_isPreorder_506 :: T_IsTotalOrder_488 -> T_IsPreorder_76
d_isPreorder_506 v0
  = coe d_isPreorder_256 (coe d_isPartialOrder_496 (coe v0))
-- Relation.Binary.Structures.IsTotalOrder._.refl
d_refl_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_488 -> AgdaAny -> AgdaAny
d_refl_508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_508 v6
du_refl_508 :: T_IsTotalOrder_488 -> AgdaAny -> AgdaAny
du_refl_508 v0
  = let v1 = d_isPartialOrder_496 (coe v0) in
    coe (coe du_refl_104 (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.reflexive
d_reflexive_510 ::
  T_IsTotalOrder_488 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_510 v0
  = coe
      d_reflexive_88
      (coe d_isPreorder_256 (coe d_isPartialOrder_496 (coe v0)))
-- Relation.Binary.Structures.IsTotalOrder._.trans
d_trans_512 ::
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_512 v0
  = coe
      d_trans_90
      (coe d_isPreorder_256 (coe d_isPartialOrder_496 (coe v0)))
-- Relation.Binary.Structures.IsTotalOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_514 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_514 v6
du_'8764''45'resp'45''8776'_514 ::
  T_IsTotalOrder_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_514 v0
  = let v1 = d_isPartialOrder_496 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'45''8776'_124 (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_516 v6
du_'8764''45'resp'691''45''8776'_516 ::
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_516 v0
  = let v1 = d_isPartialOrder_496 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'691''45''8776'_122
         (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_518 v6
du_'8764''45'resp'737''45''8776'_518 ::
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_518 v0
  = let v1 = d_isPartialOrder_496 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'737''45''8776'_120
         (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_520 v6
du_'8818''45'resp'45''8776'_520 ::
  T_IsTotalOrder_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_520 v0
  = let v1 = d_isPartialOrder_496 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'45''8776'_118 (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_522 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'691''45''8776'_522 v6
du_'8818''45'resp'691''45''8776'_522 ::
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_522 v0
  = let v1 = d_isPartialOrder_496 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'691''45''8776'_112
         (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_524 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'737''45''8776'_524 v6
du_'8818''45'resp'737''45''8776'_524 ::
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_524 v0
  = let v1 = d_isPartialOrder_496 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'737''45''8776'_106
         (coe d_isPreorder_256 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_488 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_528 v6
du_isPartialEquivalence_528 ::
  T_IsTotalOrder_488 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_528 v0
  = let v1 = d_isPartialOrder_496 (coe v0) in
    coe
      (let v2 = d_isPreorder_256 (coe v1) in
       coe
         (coe du_isPartialEquivalence_44 (coe d_isEquivalence_86 (coe v2))))
-- Relation.Binary.Structures.IsTotalOrder._.Eq.refl
d_refl_530 :: T_IsTotalOrder_488 -> AgdaAny -> AgdaAny
d_refl_530 v0
  = coe
      d_refl_36
      (coe
         d_isEquivalence_86
         (coe d_isPreorder_256 (coe d_isPartialOrder_496 (coe v0))))
-- Relation.Binary.Structures.IsTotalOrder._.Eq.reflexive
d_reflexive_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_488 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_532 v6
du_reflexive_532 ::
  T_IsTotalOrder_488 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_532 v0
  = let v1 = d_isPartialOrder_496 (coe v0) in
    coe
      (let v2 = d_isPreorder_256 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe du_reflexive_42 (coe d_isEquivalence_86 (coe v2)) v3))
-- Relation.Binary.Structures.IsTotalOrder._.Eq.sym
d_sym_534 ::
  T_IsTotalOrder_488 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_534 v0
  = coe
      d_sym_38
      (coe
         d_isEquivalence_86
         (coe d_isPreorder_256 (coe d_isPartialOrder_496 (coe v0))))
-- Relation.Binary.Structures.IsTotalOrder._.Eq.trans
d_trans_536 ::
  T_IsTotalOrder_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_536 v0
  = coe
      d_trans_40
      (coe
         d_isEquivalence_86
         (coe d_isPreorder_256 (coe d_isPartialOrder_496 (coe v0))))
-- Relation.Binary.Structures.IsTotalOrder.isTotalPreorder
d_isTotalPreorder_538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_488 -> T_IsTotalPreorder_132
d_isTotalPreorder_538 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isTotalPreorder_538 v6
du_isTotalPreorder_538 ::
  T_IsTotalOrder_488 -> T_IsTotalPreorder_132
du_isTotalPreorder_538 v0
  = coe
      C_constructor_178
      (coe d_isPreorder_256 (coe d_isPartialOrder_496 (coe v0)))
      (coe d_total_498 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder
d_IsDecTotalOrder_546 a0 a1 a2 a3 a4 a5 = ()
data T_IsDecTotalOrder_546
  = C_constructor_618 T_IsTotalOrder_488
                      (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                      (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
-- Relation.Binary.Structures.IsDecTotalOrder.isTotalOrder
d_isTotalOrder_556 :: T_IsDecTotalOrder_546 -> T_IsTotalOrder_488
d_isTotalOrder_556 v0
  = case coe v0 of
      C_constructor_618 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecTotalOrder._≟_
d__'8799'__558 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__558 v0
  = case coe v0 of
      C_constructor_618 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecTotalOrder._≤?_
d__'8804''63'__560 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__560 v0
  = case coe v0 of
      C_constructor_618 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecTotalOrder._.antisym
d_antisym_564 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_564 v0
  = coe
      d_antisym_258
      (coe d_isPartialOrder_496 (coe d_isTotalOrder_556 (coe v0)))
-- Relation.Binary.Structures.IsDecTotalOrder._.isEquivalence
d_isEquivalence_566 :: T_IsDecTotalOrder_546 -> T_IsEquivalence_28
d_isEquivalence_566 v0
  = coe
      d_isEquivalence_86
      (coe
         d_isPreorder_256
         (coe d_isPartialOrder_496 (coe d_isTotalOrder_556 (coe v0))))
-- Relation.Binary.Structures.IsDecTotalOrder._.isPartialOrder
d_isPartialOrder_568 ::
  T_IsDecTotalOrder_546 -> T_IsPartialOrder_248
d_isPartialOrder_568 v0
  = coe d_isPartialOrder_496 (coe d_isTotalOrder_556 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder._.isPreorder
d_isPreorder_570 :: T_IsDecTotalOrder_546 -> T_IsPreorder_76
d_isPreorder_570 v0
  = coe
      d_isPreorder_256
      (coe d_isPartialOrder_496 (coe d_isTotalOrder_556 (coe v0)))
-- Relation.Binary.Structures.IsDecTotalOrder._.isTotalPreorder
d_isTotalPreorder_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 -> T_IsTotalPreorder_132
d_isTotalPreorder_572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isTotalPreorder_572 v6
du_isTotalPreorder_572 ::
  T_IsDecTotalOrder_546 -> T_IsTotalPreorder_132
du_isTotalPreorder_572 v0
  = coe du_isTotalPreorder_538 (coe d_isTotalOrder_556 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder._.refl
d_refl_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 -> AgdaAny -> AgdaAny
d_refl_574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_574 v6
du_refl_574 :: T_IsDecTotalOrder_546 -> AgdaAny -> AgdaAny
du_refl_574 v0
  = let v1 = d_isTotalOrder_556 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_496 (coe v1) in
       coe (coe du_refl_104 (coe d_isPreorder_256 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.reflexive
d_reflexive_576 ::
  T_IsDecTotalOrder_546 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_576 v0
  = coe
      d_reflexive_88
      (coe
         d_isPreorder_256
         (coe d_isPartialOrder_496 (coe d_isTotalOrder_556 (coe v0))))
-- Relation.Binary.Structures.IsDecTotalOrder._.total
d_total_578 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_578 v0 = coe d_total_498 (coe d_isTotalOrder_556 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder._.trans
d_trans_580 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_580 v0
  = coe
      d_trans_90
      (coe
         d_isPreorder_256
         (coe d_isPartialOrder_496 (coe d_isTotalOrder_556 (coe v0))))
-- Relation.Binary.Structures.IsDecTotalOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_582 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_582 v6
du_'8764''45'resp'45''8776'_582 ::
  T_IsDecTotalOrder_546 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_582 v0
  = let v1 = d_isTotalOrder_556 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_496 (coe v1) in
       coe
         (coe
            du_'8764''45'resp'45''8776'_124 (coe d_isPreorder_256 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_584 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_584 v6
du_'8764''45'resp'691''45''8776'_584 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_584 v0
  = let v1 = d_isTotalOrder_556 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_496 (coe v1) in
       coe
         (coe
            du_'8764''45'resp'691''45''8776'_122
            (coe d_isPreorder_256 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_586 v6
du_'8764''45'resp'737''45''8776'_586 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_586 v0
  = let v1 = d_isTotalOrder_556 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_496 (coe v1) in
       coe
         (coe
            du_'8764''45'resp'737''45''8776'_120
            (coe d_isPreorder_256 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_588 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_588 v6
du_'8818''45'resp'45''8776'_588 ::
  T_IsDecTotalOrder_546 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_588 v0
  = let v1 = d_isTotalOrder_556 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_496 (coe v1) in
       coe
         (coe
            du_'8818''45'resp'45''8776'_118 (coe d_isPreorder_256 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_590 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'691''45''8776'_590 v6
du_'8818''45'resp'691''45''8776'_590 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_590 v0
  = let v1 = d_isTotalOrder_556 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_496 (coe v1) in
       coe
         (coe
            du_'8818''45'resp'691''45''8776'_112
            (coe d_isPreorder_256 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'737''45''8776'_592 v6
du_'8818''45'resp'737''45''8776'_592 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_592 v0
  = let v1 = d_isTotalOrder_556 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_496 (coe v1) in
       coe
         (coe
            du_'8818''45'resp'737''45''8776'_106
            (coe d_isPreorder_256 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder.isDecPartialOrder
d_isDecPartialOrder_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 -> T_IsDecPartialOrder_300
d_isDecPartialOrder_594 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecPartialOrder_594 v6
du_isDecPartialOrder_594 ::
  T_IsDecTotalOrder_546 -> T_IsDecPartialOrder_300
du_isDecPartialOrder_594 v0
  = coe
      C_constructor_364
      (coe d_isPartialOrder_496 (coe d_isTotalOrder_556 (coe v0)))
      (coe d__'8799'__558 (coe v0)) (coe d__'8804''63'__560 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder._.isDecPreorder
d_isDecPreorder_598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 -> T_IsDecPreorder_184
d_isDecPreorder_598 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecPreorder_598 v6
du_isDecPreorder_598 ::
  T_IsDecTotalOrder_546 -> T_IsDecPreorder_184
du_isDecPreorder_598 v0
  = coe du_isDecPreorder_342 (coe du_isDecPartialOrder_594 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder._.Eq._≟_
d__'8799'__602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__602 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__602 v6
du__'8799'__602 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__602 v0
  = let v1 = coe du_isDecPartialOrder_594 (coe v0) in
    coe
      (let v2 = coe du_isDecPreorder_342 (coe v1) in
       coe (coe d__'8799'__196 (coe v2)))
-- Relation.Binary.Structures.IsDecTotalOrder._.Eq.isDecEquivalence
d_isDecEquivalence_604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 -> T_IsDecEquivalence_48
d_isDecEquivalence_604 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_604 v6
du_isDecEquivalence_604 ::
  T_IsDecTotalOrder_546 -> T_IsDecEquivalence_48
du_isDecEquivalence_604 v0
  = let v1 = coe du_isDecPartialOrder_594 (coe v0) in
    coe
      (coe du_isDecEquivalence_224 (coe du_isDecPreorder_342 (coe v1)))
-- Relation.Binary.Structures.IsDecTotalOrder._.Eq.isEquivalence
d_isEquivalence_606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 -> T_IsEquivalence_28
d_isEquivalence_606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_606 v6
du_isEquivalence_606 :: T_IsDecTotalOrder_546 -> T_IsEquivalence_28
du_isEquivalence_606 v0
  = let v1 = coe du_isDecPartialOrder_594 (coe v0) in
    coe
      (let v2 = coe du_isDecPreorder_342 (coe v1) in
       coe (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_608 v6
du_isPartialEquivalence_608 ::
  T_IsDecTotalOrder_546 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_608 v0
  = let v1 = coe du_isDecPartialOrder_594 (coe v0) in
    coe
      (let v2 = coe du_isDecPreorder_342 (coe v1) in
       coe
         (let v3 = coe du_isDecEquivalence_224 (coe v2) in
          coe
            (coe
               du_isPartialEquivalence_44 (coe d_isEquivalence_54 (coe v3)))))
-- Relation.Binary.Structures.IsDecTotalOrder._.Eq.refl
d_refl_610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 -> AgdaAny -> AgdaAny
d_refl_610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_610 v6
du_refl_610 :: T_IsDecTotalOrder_546 -> AgdaAny -> AgdaAny
du_refl_610 v0
  = let v1 = coe du_isDecPartialOrder_594 (coe v0) in
    coe
      (let v2 = coe du_isDecPreorder_342 (coe v1) in
       coe
         (coe
            d_refl_36
            (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v2)))))
-- Relation.Binary.Structures.IsDecTotalOrder._.Eq.reflexive
d_reflexive_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_612 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_612 v6
du_reflexive_612 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_612 v0
  = let v1 = coe du_isDecPartialOrder_594 (coe v0) in
    coe
      (let v2 = coe du_isDecPreorder_342 (coe v1) in
       coe
         (let v3 = coe du_isDecEquivalence_224 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe du_reflexive_42 (coe d_isEquivalence_54 (coe v3)) v4)))
-- Relation.Binary.Structures.IsDecTotalOrder._.Eq.sym
d_sym_614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_614 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_614 v6
du_sym_614 ::
  T_IsDecTotalOrder_546 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_614 v0
  = let v1 = coe du_isDecPartialOrder_594 (coe v0) in
    coe
      (let v2 = coe du_isDecPreorder_342 (coe v1) in
       coe
         (coe
            d_sym_38 (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v2)))))
-- Relation.Binary.Structures.IsDecTotalOrder._.Eq.trans
d_trans_616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_616 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_616 v6
du_trans_616 ::
  T_IsDecTotalOrder_546 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_616 v0
  = let v1 = coe du_isDecPartialOrder_594 (coe v0) in
    coe
      (let v2 = coe du_isDecPreorder_342 (coe v1) in
       coe
         (coe
            d_trans_40
            (coe d_isEquivalence_86 (coe d_isPreorder_194 (coe v2)))))
-- Relation.Binary.Structures.IsStrictTotalOrder
d_IsStrictTotalOrder_624 a0 a1 a2 a3 a4 a5 = ()
data T_IsStrictTotalOrder_624
  = C_constructor_680 T_IsStrictPartialOrder_370
                      (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158)
-- Relation.Binary.Structures.IsStrictTotalOrder.isStrictPartialOrder
d_isStrictPartialOrder_632 ::
  T_IsStrictTotalOrder_624 -> T_IsStrictPartialOrder_370
d_isStrictPartialOrder_632 v0
  = case coe v0 of
      C_constructor_680 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsStrictTotalOrder.compare
d_compare_634 ::
  T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_634 v0
  = case coe v0 of
      C_constructor_680 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsStrictTotalOrder._.<-resp-≈
d_'60''45'resp'45''8776'_638 ::
  T_IsStrictTotalOrder_624 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_638 v0
  = coe
      d_'60''45'resp'45''8776'_388
      (coe d_isStrictPartialOrder_632 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_640 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'691''45''8776'_640 v6
du_'60''45'resp'691''45''8776'_640 ::
  T_IsStrictTotalOrder_624 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_640 v0
  = coe
      du_'60''45'resp'691''45''8776'_408
      (coe d_isStrictPartialOrder_632 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_642 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'737''45''8776'_642 v6
du_'60''45'resp'737''45''8776'_642 ::
  T_IsStrictTotalOrder_624 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_642 v0
  = coe
      du_'60''45'resp'737''45''8776'_410
      (coe d_isStrictPartialOrder_632 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._.asym
d_asym_644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_644 = erased
-- Relation.Binary.Structures.IsStrictTotalOrder._.irrefl
d_irrefl_646 ::
  T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_646 = erased
-- Relation.Binary.Structures.IsStrictTotalOrder._.isEquivalence
d_isEquivalence_648 ::
  T_IsStrictTotalOrder_624 -> T_IsEquivalence_28
d_isEquivalence_648 v0
  = coe d_isEquivalence_382 (coe d_isStrictPartialOrder_632 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._.trans
d_trans_650 ::
  T_IsStrictTotalOrder_624 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_650 v0
  = coe d_trans_386 (coe d_isStrictPartialOrder_632 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._≟_
d__'8799'__652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__652 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__652 v6
du__'8799'__652 ::
  T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__652 v0
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_tri'8658'dec'8776'_548
      (coe d_compare_634 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._<?_
d__'60''63'__654 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__654 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'60''63'__654 v6
du__'60''63'__654 ::
  T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'60''63'__654 v0
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_tri'8658'dec'60'_584
      (coe d_compare_634 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder.isDecStrictPartialOrder
d_isDecStrictPartialOrder_656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 -> T_IsDecStrictPartialOrder_418
d_isDecStrictPartialOrder_656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecStrictPartialOrder_656 v6
du_isDecStrictPartialOrder_656 ::
  T_IsStrictTotalOrder_624 -> T_IsDecStrictPartialOrder_418
du_isDecStrictPartialOrder_656 v0
  = coe
      C_constructor_482 (coe d_isStrictPartialOrder_632 (coe v0))
      (coe du__'8799'__652 (coe v0)) (coe du__'60''63'__654 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq.isDecEquivalence
d_isDecEquivalence_660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 -> T_IsDecEquivalence_48
d_isDecEquivalence_660 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_660 v6
du_isDecEquivalence_660 ::
  T_IsStrictTotalOrder_624 -> T_IsDecEquivalence_48
du_isDecEquivalence_660 v0
  = coe
      C_constructor_70
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_632 (coe v0)))
      (coe du__'8799'__652 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._._≟_
d__'8799'__664 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__664 v6
du__'8799'__664 ::
  T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__664 v0 = coe du__'8799'__652 (coe v0)
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.isEquivalence
d_isEquivalence_666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 -> T_IsEquivalence_28
d_isEquivalence_666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_666 v6
du_isEquivalence_666 ::
  T_IsStrictTotalOrder_624 -> T_IsEquivalence_28
du_isEquivalence_666 v0
  = coe d_isEquivalence_382 (coe d_isStrictPartialOrder_632 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.isPartialEquivalence
d_isPartialEquivalence_668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_668 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_668 v6
du_isPartialEquivalence_668 ::
  T_IsStrictTotalOrder_624 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_668 v0
  = let v1 = coe du_isDecEquivalence_660 (coe v0) in
    coe
      (coe du_isPartialEquivalence_44 (coe d_isEquivalence_54 (coe v1)))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.refl
d_refl_670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 -> AgdaAny -> AgdaAny
d_refl_670 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_670 v6
du_refl_670 :: T_IsStrictTotalOrder_624 -> AgdaAny -> AgdaAny
du_refl_670 v0
  = coe
      d_refl_36
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_632 (coe v0)))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.reflexive
d_reflexive_672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_672 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_672 v6
du_reflexive_672 ::
  T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_672 v0
  = let v1 = coe du_isDecEquivalence_660 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_42 (coe d_isEquivalence_54 (coe v1)) v2)
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.sym
d_sym_674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_674 v6
du_sym_674 ::
  T_IsStrictTotalOrder_624 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_674 v0
  = coe
      d_sym_38
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_632 (coe v0)))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.trans
d_trans_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_676 v6
du_trans_676 ::
  T_IsStrictTotalOrder_624 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_676 v0
  = coe
      d_trans_40
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_632 (coe v0)))
-- Relation.Binary.Structures.IsStrictTotalOrder.isDecEquivalence
d_isDecEquivalence_678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_624 -> T_IsDecEquivalence_48
d_isDecEquivalence_678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_678 v6
du_isDecEquivalence_678 ::
  T_IsStrictTotalOrder_624 -> T_IsDecEquivalence_48
du_isDecEquivalence_678 v0
  = coe
      C_constructor_70
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_632 (coe v0)))
      (coe du__'8799'__652 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder
d_IsDenseLinearOrder_686 a0 a1 a2 a3 a4 a5 = ()
data T_IsDenseLinearOrder_686
  = C_constructor_744 T_IsStrictTotalOrder_624
                      (AgdaAny ->
                       AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Structures.IsDenseLinearOrder.isStrictTotalOrder
d_isStrictTotalOrder_694 ::
  T_IsDenseLinearOrder_686 -> T_IsStrictTotalOrder_624
d_isStrictTotalOrder_694 v0
  = case coe v0 of
      C_constructor_744 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDenseLinearOrder.dense
d_dense_696 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dense_696 v0
  = case coe v0 of
      C_constructor_744 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDenseLinearOrder._._<?_
d__'60''63'__700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'60''63'__700 v6
du__'60''63'__700 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'60''63'__700 v0
  = coe du__'60''63'__654 (coe d_isStrictTotalOrder_694 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._._≟_
d__'8799'__702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__702 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__702 v6
du__'8799'__702 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__702 v0
  = coe du__'8799'__652 (coe d_isStrictTotalOrder_694 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.<-resp-≈
d_'60''45'resp'45''8776'_704 ::
  T_IsDenseLinearOrder_686 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_704 v0
  = coe
      d_'60''45'resp'45''8776'_388
      (coe
         d_isStrictPartialOrder_632 (coe d_isStrictTotalOrder_694 (coe v0)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'691''45''8776'_706 v6
du_'60''45'resp'691''45''8776'_706 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_706 v0
  = let v1 = d_isStrictTotalOrder_694 (coe v0) in
    coe
      (coe
         du_'60''45'resp'691''45''8776'_408
         (coe d_isStrictPartialOrder_632 (coe v1)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'737''45''8776'_708 v6
du_'60''45'resp'737''45''8776'_708 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_708 v0
  = let v1 = d_isStrictTotalOrder_694 (coe v0) in
    coe
      (coe
         du_'60''45'resp'737''45''8776'_410
         (coe d_isStrictPartialOrder_632 (coe v1)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.asym
d_asym_710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_710 = erased
-- Relation.Binary.Structures.IsDenseLinearOrder._.compare
d_compare_712 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_712 v0
  = coe d_compare_634 (coe d_isStrictTotalOrder_694 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.irrefl
d_irrefl_714 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_714 = erased
-- Relation.Binary.Structures.IsDenseLinearOrder._.isDecEquivalence
d_isDecEquivalence_716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 -> T_IsDecEquivalence_48
d_isDecEquivalence_716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_716 v6
du_isDecEquivalence_716 ::
  T_IsDenseLinearOrder_686 -> T_IsDecEquivalence_48
du_isDecEquivalence_716 v0
  = coe
      du_isDecEquivalence_678 (coe d_isStrictTotalOrder_694 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.isDecStrictPartialOrder
d_isDecStrictPartialOrder_718 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 -> T_IsDecStrictPartialOrder_418
d_isDecStrictPartialOrder_718 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecStrictPartialOrder_718 v6
du_isDecStrictPartialOrder_718 ::
  T_IsDenseLinearOrder_686 -> T_IsDecStrictPartialOrder_418
du_isDecStrictPartialOrder_718 v0
  = coe
      du_isDecStrictPartialOrder_656
      (coe d_isStrictTotalOrder_694 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.isEquivalence
d_isEquivalence_720 ::
  T_IsDenseLinearOrder_686 -> T_IsEquivalence_28
d_isEquivalence_720 v0
  = coe
      d_isEquivalence_382
      (coe
         d_isStrictPartialOrder_632 (coe d_isStrictTotalOrder_694 (coe v0)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.isStrictPartialOrder
d_isStrictPartialOrder_722 ::
  T_IsDenseLinearOrder_686 -> T_IsStrictPartialOrder_370
d_isStrictPartialOrder_722 v0
  = coe
      d_isStrictPartialOrder_632 (coe d_isStrictTotalOrder_694 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.trans
d_trans_724 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_724 v0
  = coe
      d_trans_386
      (coe
         d_isStrictPartialOrder_632 (coe d_isStrictTotalOrder_694 (coe v0)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq._≟_
d__'8799'__728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__728 v6
du__'8799'__728 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__728 v0
  = let v1 = d_isStrictTotalOrder_694 (coe v0) in
    coe (coe du__'8799'__652 (coe v1))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.isDecEquivalence
d_isDecEquivalence_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 -> T_IsDecEquivalence_48
d_isDecEquivalence_730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_730 v6
du_isDecEquivalence_730 ::
  T_IsDenseLinearOrder_686 -> T_IsDecEquivalence_48
du_isDecEquivalence_730 v0
  = coe
      du_isDecEquivalence_660 (coe d_isStrictTotalOrder_694 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.isEquivalence
d_isEquivalence_732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 -> T_IsEquivalence_28
d_isEquivalence_732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_732 v6
du_isEquivalence_732 ::
  T_IsDenseLinearOrder_686 -> T_IsEquivalence_28
du_isEquivalence_732 v0
  = let v1 = d_isStrictTotalOrder_694 (coe v0) in
    coe
      (coe d_isEquivalence_382 (coe d_isStrictPartialOrder_632 (coe v1)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_734 v6
du_isPartialEquivalence_734 ::
  T_IsDenseLinearOrder_686 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_734 v0
  = let v1 = d_isStrictTotalOrder_694 (coe v0) in
    coe
      (let v2 = coe du_isDecEquivalence_660 (coe v1) in
       coe
         (coe du_isPartialEquivalence_44 (coe d_isEquivalence_54 (coe v2))))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.refl
d_refl_736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 -> AgdaAny -> AgdaAny
d_refl_736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_736 v6
du_refl_736 :: T_IsDenseLinearOrder_686 -> AgdaAny -> AgdaAny
du_refl_736 v0
  = let v1 = d_isStrictTotalOrder_694 (coe v0) in
    coe
      (coe
         d_refl_36
         (coe
            d_isEquivalence_382 (coe d_isStrictPartialOrder_632 (coe v1))))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.reflexive
d_reflexive_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_738 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_738 v6
du_reflexive_738 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_738 v0
  = let v1 = d_isStrictTotalOrder_694 (coe v0) in
    coe
      (let v2 = coe du_isDecEquivalence_660 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe du_reflexive_42 (coe d_isEquivalence_54 (coe v2)) v3))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.sym
d_sym_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_740 v6
du_sym_740 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_740 v0
  = let v1 = d_isStrictTotalOrder_694 (coe v0) in
    coe
      (coe
         d_sym_38
         (coe
            d_isEquivalence_382 (coe d_isStrictPartialOrder_632 (coe v1))))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.trans
d_trans_742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_742 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_742 v6
du_trans_742 ::
  T_IsDenseLinearOrder_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_742 v0
  = let v1 = d_isStrictTotalOrder_694 (coe v0) in
    coe
      (coe
         d_trans_40
         (coe
            d_isEquivalence_382 (coe d_isStrictPartialOrder_632 (coe v1))))
-- Relation.Binary.Structures.IsApartnessRelation
d_IsApartnessRelation_750 a0 a1 a2 a3 a4 a5 = ()
data T_IsApartnessRelation_750
  = C_constructor_772 (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny ->
                       AgdaAny ->
                       AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Relation.Binary.Structures.IsApartnessRelation.irrefl
d_irrefl_760 ::
  T_IsApartnessRelation_750 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_760 = erased
-- Relation.Binary.Structures.IsApartnessRelation.sym
d_sym_762 ::
  T_IsApartnessRelation_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_762 v0
  = case coe v0 of
      C_constructor_772 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsApartnessRelation.cotrans
d_cotrans_764 ::
  T_IsApartnessRelation_750 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cotrans_764 v0
  = case coe v0 of
      C_constructor_772 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsApartnessRelation._¬#_
d__'172''35'__766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsApartnessRelation_750 -> AgdaAny -> AgdaAny -> ()
d__'172''35'__766 = erased
