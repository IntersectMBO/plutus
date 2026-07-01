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

module MAlonzo.Code.Relation.Binary.Bundles where

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
import qualified MAlonzo.Code.Relation.Binary.Bundles.Raw
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.Bundles.PartialSetoid
d_PartialSetoid_10 a0 a1 = ()
newtype T_PartialSetoid_10
  = C_constructor_40 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
-- Relation.Binary.Bundles.PartialSetoid.Carrier
d_Carrier_22 :: T_PartialSetoid_10 -> ()
d_Carrier_22 = erased
-- Relation.Binary.Bundles.PartialSetoid._≈_
d__'8776'__24 :: T_PartialSetoid_10 -> AgdaAny -> AgdaAny -> ()
d__'8776'__24 = erased
-- Relation.Binary.Bundles.PartialSetoid.isPartialEquivalence
d_isPartialEquivalence_26 ::
  T_PartialSetoid_10 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_26 v0
  = case coe v0 of
      C_constructor_40 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.PartialSetoid._.sym
d_sym_30 ::
  T_PartialSetoid_10 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_30 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_22
      (coe d_isPartialEquivalence_26 (coe v0))
-- Relation.Binary.Bundles.PartialSetoid._.trans
d_trans_32 ::
  T_PartialSetoid_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_32 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_24
      (coe d_isPartialEquivalence_26 (coe v0))
-- Relation.Binary.Bundles.PartialSetoid.rawSetoid
d_rawSetoid_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PartialSetoid_10 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_34 = erased
-- Relation.Binary.Bundles.PartialSetoid._._≉_
d__'8777'__38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PartialSetoid_10 -> AgdaAny -> AgdaAny -> ()
d__'8777'__38 = erased
-- Relation.Binary.Bundles.Setoid
d_Setoid_46 a0 a1 = ()
newtype T_Setoid_46
  = C_constructor_84 MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
-- Relation.Binary.Bundles.Setoid.Carrier
d_Carrier_58 :: T_Setoid_46 -> ()
d_Carrier_58 = erased
-- Relation.Binary.Bundles.Setoid._≈_
d__'8776'__60 :: T_Setoid_46 -> AgdaAny -> AgdaAny -> ()
d__'8776'__60 = erased
-- Relation.Binary.Bundles.Setoid.isEquivalence
d_isEquivalence_62 ::
  T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_62 v0
  = case coe v0 of
      C_constructor_84 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.Setoid._.isPartialEquivalence
d_isPartialEquivalence_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_66 ~v0 ~v1 v2
  = du_isPartialEquivalence_66 v2
du_isPartialEquivalence_66 ::
  T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_66 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe d_isEquivalence_62 (coe v0))
-- Relation.Binary.Bundles.Setoid._.refl
d_refl_68 :: T_Setoid_46 -> AgdaAny -> AgdaAny
d_refl_68 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_62 (coe v0))
-- Relation.Binary.Bundles.Setoid._.reflexive
d_reflexive_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_46 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_70 ~v0 ~v1 v2 = du_reflexive_70 v2
du_reflexive_70 ::
  T_Setoid_46 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_70 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
      (coe d_isEquivalence_62 (coe v0)) v1
-- Relation.Binary.Bundles.Setoid.partialSetoid
d_partialSetoid_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_46 -> T_PartialSetoid_10
d_partialSetoid_72 ~v0 ~v1 v2 = du_partialSetoid_72 v2
du_partialSetoid_72 :: T_Setoid_46 -> T_PartialSetoid_10
du_partialSetoid_72 v0
  = coe
      C_constructor_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_62 (coe v0)))
-- Relation.Binary.Bundles.Setoid._._≉_
d__'8777'__76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_46 -> AgdaAny -> AgdaAny -> ()
d__'8777'__76 = erased
-- Relation.Binary.Bundles.Setoid._.rawSetoid
d_rawSetoid_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_78 = erased
-- Relation.Binary.Bundles.Setoid._.sym
d_sym_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_46 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_80 ~v0 ~v1 v2 = du_sym_80 v2
du_sym_80 ::
  T_Setoid_46 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_80 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_62 (coe v0))
-- Relation.Binary.Bundles.Setoid._.trans
d_trans_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_46 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_82 ~v0 ~v1 v2 = du_trans_82 v2
du_trans_82 ::
  T_Setoid_46 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_82 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_62 (coe v0))
-- Relation.Binary.Bundles.DecSetoid
d_DecSetoid_90 a0 a1 = ()
newtype T_DecSetoid_90
  = C_constructor_134 MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
-- Relation.Binary.Bundles.DecSetoid.Carrier
d_Carrier_102 :: T_DecSetoid_90 -> ()
d_Carrier_102 = erased
-- Relation.Binary.Bundles.DecSetoid._≈_
d__'8776'__104 :: T_DecSetoid_90 -> AgdaAny -> AgdaAny -> ()
d__'8776'__104 = erased
-- Relation.Binary.Bundles.DecSetoid.isDecEquivalence
d_isDecEquivalence_106 ::
  T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_106 v0
  = case coe v0 of
      C_constructor_134 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.DecSetoid._._≟_
d__'8799'__110 ::
  T_DecSetoid_90 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__110 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__56
      (coe d_isDecEquivalence_106 (coe v0))
-- Relation.Binary.Bundles.DecSetoid._.isEquivalence
d_isEquivalence_112 ::
  T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_112 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
      (coe d_isDecEquivalence_106 (coe v0))
-- Relation.Binary.Bundles.DecSetoid.setoid
d_setoid_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_90 -> T_Setoid_46
d_setoid_114 ~v0 ~v1 v2 = du_setoid_114 v2
du_setoid_114 :: T_DecSetoid_90 -> T_Setoid_46
du_setoid_114 v0
  = coe
      C_constructor_84
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
         (coe d_isDecEquivalence_106 (coe v0)))
-- Relation.Binary.Bundles.DecSetoid._._≉_
d__'8777'__118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_90 -> AgdaAny -> AgdaAny -> ()
d__'8777'__118 = erased
-- Relation.Binary.Bundles.DecSetoid._.isPartialEquivalence
d_isPartialEquivalence_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_120 ~v0 ~v1 v2
  = du_isPartialEquivalence_120 v2
du_isPartialEquivalence_120 ::
  T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_120 v0
  = let v1 = coe du_setoid_114 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_62 (coe v1)))
-- Relation.Binary.Bundles.DecSetoid._.partialSetoid
d_partialSetoid_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_90 -> T_PartialSetoid_10
d_partialSetoid_122 ~v0 ~v1 v2 = du_partialSetoid_122 v2
du_partialSetoid_122 :: T_DecSetoid_90 -> T_PartialSetoid_10
du_partialSetoid_122 v0
  = coe du_partialSetoid_72 (coe du_setoid_114 (coe v0))
-- Relation.Binary.Bundles.DecSetoid._.rawSetoid
d_rawSetoid_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_124 = erased
-- Relation.Binary.Bundles.DecSetoid._.refl
d_refl_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_90 -> AgdaAny -> AgdaAny
d_refl_126 ~v0 ~v1 v2 = du_refl_126 v2
du_refl_126 :: T_DecSetoid_90 -> AgdaAny -> AgdaAny
du_refl_126 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
         (coe d_isDecEquivalence_106 (coe v0)))
-- Relation.Binary.Bundles.DecSetoid._.reflexive
d_reflexive_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_90 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_128 ~v0 ~v1 v2 = du_reflexive_128 v2
du_reflexive_128 ::
  T_DecSetoid_90 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_128 v0
  = let v1 = coe du_setoid_114 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_62 (coe v1)) v2)
-- Relation.Binary.Bundles.DecSetoid._.sym
d_sym_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_90 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_130 ~v0 ~v1 v2 = du_sym_130 v2
du_sym_130 ::
  T_DecSetoid_90 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_130 v0
  = let v1 = coe du_setoid_114 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe d_isEquivalence_62 (coe v1)))
-- Relation.Binary.Bundles.DecSetoid._.trans
d_trans_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_90 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_132 ~v0 ~v1 v2 = du_trans_132 v2
du_trans_132 ::
  T_DecSetoid_90 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_132 v0
  = let v1 = coe du_setoid_114 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe d_isEquivalence_62 (coe v1)))
-- Relation.Binary.Bundles.Preorder
d_Preorder_142 a0 a1 a2 = ()
newtype T_Preorder_142
  = C_constructor_232 MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
-- Relation.Binary.Bundles.Preorder.Carrier
d_Carrier_158 :: T_Preorder_142 -> ()
d_Carrier_158 = erased
-- Relation.Binary.Bundles.Preorder._≈_
d__'8776'__160 :: T_Preorder_142 -> AgdaAny -> AgdaAny -> ()
d__'8776'__160 = erased
-- Relation.Binary.Bundles.Preorder._≲_
d__'8818'__162 :: T_Preorder_142 -> AgdaAny -> AgdaAny -> ()
d__'8818'__162 = erased
-- Relation.Binary.Bundles.Preorder.isPreorder
d_isPreorder_164 ::
  T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_164 v0
  = case coe v0 of
      C_constructor_232 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.Preorder._.isEquivalence
d_isEquivalence_168 ::
  T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_168 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe d_isPreorder_164 (coe v0))
-- Relation.Binary.Bundles.Preorder._.refl
d_refl_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> AgdaAny -> AgdaAny
d_refl_170 ~v0 ~v1 ~v2 v3 = du_refl_170 v3
du_refl_170 :: T_Preorder_142 -> AgdaAny -> AgdaAny
du_refl_170 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_refl_104
      (coe d_isPreorder_164 (coe v0))
-- Relation.Binary.Bundles.Preorder._.reflexive
d_reflexive_172 ::
  T_Preorder_142 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_172 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe d_isPreorder_164 (coe v0))
-- Relation.Binary.Bundles.Preorder._.trans
d_trans_174 ::
  T_Preorder_142 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_174 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe d_isPreorder_164 (coe v0))
-- Relation.Binary.Bundles.Preorder._.∼-resp-≈
d_'8764''45'resp'45''8776'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_176 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_176 v3
du_'8764''45'resp'45''8776'_176 ::
  T_Preorder_142 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
      (coe d_isPreorder_164 (coe v0))
-- Relation.Binary.Bundles.Preorder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_178 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_178 v3
du_'8764''45'resp'691''45''8776'_178 ::
  T_Preorder_142 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_178 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
      (coe d_isPreorder_164 (coe v0))
-- Relation.Binary.Bundles.Preorder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_180 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_180 v3
du_'8764''45'resp'737''45''8776'_180 ::
  T_Preorder_142 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_180 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
      (coe d_isPreorder_164 (coe v0))
-- Relation.Binary.Bundles.Preorder._.≲-resp-≈
d_'8818''45'resp'45''8776'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_182 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_182 v3
du_'8818''45'resp'45''8776'_182 ::
  T_Preorder_142 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_182 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
      (coe d_isPreorder_164 (coe v0))
-- Relation.Binary.Bundles.Preorder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_184 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_184 v3
du_'8818''45'resp'691''45''8776'_184 ::
  T_Preorder_142 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_184 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
      (coe d_isPreorder_164 (coe v0))
-- Relation.Binary.Bundles.Preorder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_186 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_186 v3
du_'8818''45'resp'737''45''8776'_186 ::
  T_Preorder_142 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_186 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
      (coe d_isPreorder_164 (coe v0))
-- Relation.Binary.Bundles.Preorder.Eq.setoid
d_setoid_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> T_Setoid_46
d_setoid_190 ~v0 ~v1 ~v2 v3 = du_setoid_190 v3
du_setoid_190 :: T_Preorder_142 -> T_Setoid_46
du_setoid_190 v0
  = coe
      C_constructor_84
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe d_isPreorder_164 (coe v0)))
-- Relation.Binary.Bundles.Preorder.Eq._._≈_
d__'8776'__194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> AgdaAny -> AgdaAny -> ()
d__'8776'__194 = erased
-- Relation.Binary.Bundles.Preorder.Eq._._≉_
d__'8777'__196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> AgdaAny -> AgdaAny -> ()
d__'8777'__196 = erased
-- Relation.Binary.Bundles.Preorder.Eq._.Carrier
d_Carrier_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_Preorder_142 -> ()
d_Carrier_198 = erased
-- Relation.Binary.Bundles.Preorder.Eq._.isEquivalence
d_isEquivalence_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_200 ~v0 ~v1 ~v2 v3 = du_isEquivalence_200 v3
du_isEquivalence_200 ::
  T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_200 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe d_isPreorder_164 (coe v0))
-- Relation.Binary.Bundles.Preorder.Eq._.isPartialEquivalence
d_isPartialEquivalence_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_202 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_202 v3
du_isPartialEquivalence_202 ::
  T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_202 v0
  = let v1 = coe du_setoid_190 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_62 (coe v1)))
-- Relation.Binary.Bundles.Preorder.Eq._.partialSetoid
d_partialSetoid_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> T_PartialSetoid_10
d_partialSetoid_204 ~v0 ~v1 ~v2 v3 = du_partialSetoid_204 v3
du_partialSetoid_204 :: T_Preorder_142 -> T_PartialSetoid_10
du_partialSetoid_204 v0
  = coe du_partialSetoid_72 (coe du_setoid_190 (coe v0))
-- Relation.Binary.Bundles.Preorder.Eq._.rawSetoid
d_rawSetoid_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_206 = erased
-- Relation.Binary.Bundles.Preorder.Eq._.refl
d_refl_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> AgdaAny -> AgdaAny
d_refl_208 ~v0 ~v1 ~v2 v3 = du_refl_208 v3
du_refl_208 :: T_Preorder_142 -> AgdaAny -> AgdaAny
du_refl_208 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe d_isPreorder_164 (coe v0)))
-- Relation.Binary.Bundles.Preorder.Eq._.reflexive
d_reflexive_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_210 ~v0 ~v1 ~v2 v3 = du_reflexive_210 v3
du_reflexive_210 ::
  T_Preorder_142 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_210 v0
  = let v1 = coe du_setoid_190 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_62 (coe v1)) v2)
-- Relation.Binary.Bundles.Preorder.Eq._.sym
d_sym_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_212 ~v0 ~v1 ~v2 v3 = du_sym_212 v3
du_sym_212 ::
  T_Preorder_142 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_212 v0
  = let v1 = coe du_setoid_190 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe d_isEquivalence_62 (coe v1)))
-- Relation.Binary.Bundles.Preorder.Eq._.trans
d_trans_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_214 ~v0 ~v1 ~v2 v3 = du_trans_214 v3
du_trans_214 ::
  T_Preorder_142 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_214 v0
  = let v1 = coe du_setoid_190 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe d_isEquivalence_62 (coe v1)))
-- Relation.Binary.Bundles.Preorder.rawRelation
d_rawRelation_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_216 = erased
-- Relation.Binary.Bundles.Preorder._._∼_
d__'8764'__220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> AgdaAny -> AgdaAny -> ()
d__'8764'__220 = erased
-- Relation.Binary.Bundles.Preorder._._≉_
d__'8777'__222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> AgdaAny -> AgdaAny -> ()
d__'8777'__222 = erased
-- Relation.Binary.Bundles.Preorder._._∼ᵒ_
d__'8764''7506'__224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__224 = erased
-- Relation.Binary.Bundles.Preorder._._≁_
d__'8769'__226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> AgdaAny -> AgdaAny -> ()
d__'8769'__226 = erased
-- Relation.Binary.Bundles.Preorder._._≁ᵒ_
d__'8769''7506'__228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__228 = erased
-- Relation.Binary.Bundles.Preorder._.rawSetoid
d_rawSetoid_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_230 = erased
-- Relation.Binary.Bundles.TotalPreorder
d_TotalPreorder_240 a0 a1 a2 = ()
newtype T_TotalPreorder_240
  = C_constructor_334 MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132
-- Relation.Binary.Bundles.TotalPreorder.Carrier
d_Carrier_256 :: T_TotalPreorder_240 -> ()
d_Carrier_256 = erased
-- Relation.Binary.Bundles.TotalPreorder._≈_
d__'8776'__258 :: T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> ()
d__'8776'__258 = erased
-- Relation.Binary.Bundles.TotalPreorder._≲_
d__'8818'__260 :: T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> ()
d__'8818'__260 = erased
-- Relation.Binary.Bundles.TotalPreorder.isTotalPreorder
d_isTotalPreorder_262 ::
  T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132
d_isTotalPreorder_262 v0
  = case coe v0 of
      C_constructor_334 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.TotalPreorder._.isPreorder
d_isPreorder_266 ::
  T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_266 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
      (coe d_isTotalPreorder_262 (coe v0))
-- Relation.Binary.Bundles.TotalPreorder._.total
d_total_268 ::
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_268 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_total_142
      (coe d_isTotalPreorder_262 (coe v0))
-- Relation.Binary.Bundles.TotalPreorder.preorder
d_preorder_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> T_Preorder_142
d_preorder_270 ~v0 ~v1 ~v2 v3 = du_preorder_270 v3
du_preorder_270 :: T_TotalPreorder_240 -> T_Preorder_142
du_preorder_270 v0
  = coe
      C_constructor_232
      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
         (coe d_isTotalPreorder_262 (coe v0)))
-- Relation.Binary.Bundles.TotalPreorder._._∼_
d__'8764'__274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> ()
d__'8764'__274 = erased
-- Relation.Binary.Bundles.TotalPreorder._._≉_
d__'8777'__276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> ()
d__'8777'__276 = erased
-- Relation.Binary.Bundles.TotalPreorder._._∼ᵒ_
d__'8764''7506'__278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__278 = erased
-- Relation.Binary.Bundles.TotalPreorder._._≁_
d__'8769'__280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> ()
d__'8769'__280 = erased
-- Relation.Binary.Bundles.TotalPreorder._._≁ᵒ_
d__'8769''7506'__282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__282 = erased
-- Relation.Binary.Bundles.TotalPreorder._.isEquivalence
d_isEquivalence_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_284 ~v0 ~v1 ~v2 v3 = du_isEquivalence_284 v3
du_isEquivalence_284 ::
  T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_284 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
         (coe d_isTotalPreorder_262 (coe v0)))
-- Relation.Binary.Bundles.TotalPreorder._.rawRelation
d_rawRelation_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_286 = erased
-- Relation.Binary.Bundles.TotalPreorder._.rawSetoid
d_rawSetoid_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_288 = erased
-- Relation.Binary.Bundles.TotalPreorder._.refl
d_refl_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny
d_refl_290 ~v0 ~v1 ~v2 v3 = du_refl_290 v3
du_refl_290 :: T_TotalPreorder_240 -> AgdaAny -> AgdaAny
du_refl_290 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.reflexive
d_reflexive_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_292 ~v0 ~v1 ~v2 v3 = du_reflexive_292 v3
du_reflexive_292 ::
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_292 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
         (coe d_isTotalPreorder_262 (coe v0)))
-- Relation.Binary.Bundles.TotalPreorder._.trans
d_trans_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_294 ~v0 ~v1 ~v2 v3 = du_trans_294 v3
du_trans_294 ::
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_294 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
         (coe d_isTotalPreorder_262 (coe v0)))
-- Relation.Binary.Bundles.TotalPreorder._.∼-resp-≈
d_'8764''45'resp'45''8776'_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_296 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_296 v3
du_'8764''45'resp'45''8776'_296 ::
  T_TotalPreorder_240 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_296 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_298 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_298 v3
du_'8764''45'resp'691''45''8776'_298 ::
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_298 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_300 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_300 v3
du_'8764''45'resp'737''45''8776'_300 ::
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_300 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.≲-resp-≈
d_'8818''45'resp'45''8776'_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_302 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_302 v3
du_'8818''45'resp'45''8776'_302 ::
  T_TotalPreorder_240 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_302 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_304 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_304 v3
du_'8818''45'resp'691''45''8776'_304 ::
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_304 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_306 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_306 v3
du_'8818''45'resp'737''45''8776'_306 ::
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_306 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.Eq._≈_
d__'8776'__310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> ()
d__'8776'__310 = erased
-- Relation.Binary.Bundles.TotalPreorder._.Eq._≉_
d__'8777'__312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> ()
d__'8777'__312 = erased
-- Relation.Binary.Bundles.TotalPreorder._.Eq.Carrier
d_Carrier_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_TotalPreorder_240 -> ()
d_Carrier_314 = erased
-- Relation.Binary.Bundles.TotalPreorder._.Eq.isEquivalence
d_isEquivalence_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_316 ~v0 ~v1 ~v2 v3 = du_isEquivalence_316 v3
du_isEquivalence_316 ::
  T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_316 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.isPartialEquivalence
d_isPartialEquivalence_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_318 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_318 v3
du_isPartialEquivalence_318 ::
  T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_318 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (let v2 = coe du_setoid_190 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.partialSetoid
d_partialSetoid_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> T_PartialSetoid_10
d_partialSetoid_320 ~v0 ~v1 ~v2 v3 = du_partialSetoid_320 v3
du_partialSetoid_320 :: T_TotalPreorder_240 -> T_PartialSetoid_10
du_partialSetoid_320 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe (coe du_partialSetoid_72 (coe du_setoid_190 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.rawSetoid
d_rawSetoid_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_322 = erased
-- Relation.Binary.Bundles.TotalPreorder._.Eq.refl
d_refl_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny
d_refl_324 ~v0 ~v1 ~v2 v3 = du_refl_324 v3
du_refl_324 :: T_TotalPreorder_240 -> AgdaAny -> AgdaAny
du_refl_324 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe d_isPreorder_164 (coe v1))))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.reflexive
d_reflexive_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_326 ~v0 ~v1 ~v2 v3 = du_reflexive_326 v3
du_reflexive_326 ::
  T_TotalPreorder_240 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_326 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (let v2 = coe du_setoid_190 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe d_isEquivalence_62 (coe v2)) v3))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.setoid
d_setoid_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> T_Setoid_46
d_setoid_328 ~v0 ~v1 ~v2 v3 = du_setoid_328 v3
du_setoid_328 :: T_TotalPreorder_240 -> T_Setoid_46
du_setoid_328 v0 = coe du_setoid_190 (coe du_preorder_270 (coe v0))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.sym
d_sym_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_330 ~v0 ~v1 ~v2 v3 = du_sym_330 v3
du_sym_330 ::
  T_TotalPreorder_240 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_330 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (let v2 = coe du_setoid_190 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.trans
d_trans_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_332 ~v0 ~v1 ~v2 v3 = du_trans_332 v3
du_trans_332 ::
  T_TotalPreorder_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_332 v0
  = let v1 = coe du_preorder_270 (coe v0) in
    coe
      (let v2 = coe du_setoid_190 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.DecPreorder
d_DecPreorder_342 a0 a1 a2 = ()
newtype T_DecPreorder_342
  = C_constructor_484 MAlonzo.Code.Relation.Binary.Structures.T_IsDecPreorder_184
-- Relation.Binary.Bundles.DecPreorder.Carrier
d_Carrier_358 :: T_DecPreorder_342 -> ()
d_Carrier_358 = erased
-- Relation.Binary.Bundles.DecPreorder._≈_
d__'8776'__360 :: T_DecPreorder_342 -> AgdaAny -> AgdaAny -> ()
d__'8776'__360 = erased
-- Relation.Binary.Bundles.DecPreorder._≲_
d__'8818'__362 :: T_DecPreorder_342 -> AgdaAny -> AgdaAny -> ()
d__'8818'__362 = erased
-- Relation.Binary.Bundles.DecPreorder.isDecPreorder
d_isDecPreorder_364 ::
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPreorder_184
d_isDecPreorder_364 v0
  = case coe v0 of
      C_constructor_484 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.DecPreorder.DPO._≟_
d__'8799'__368 ::
  T_DecPreorder_342 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__368 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__196
      (coe d_isDecPreorder_364 (coe v0))
-- Relation.Binary.Bundles.DecPreorder.DPO._≲?_
d__'8818''63'__370 ::
  T_DecPreorder_342 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8818''63'__370 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8818''63'__198
      (coe d_isDecPreorder_364 (coe v0))
-- Relation.Binary.Bundles.DecPreorder.DPO.isPreorder
d_isPreorder_374 ::
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_374 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_194
      (coe d_isDecPreorder_364 (coe v0))
-- Relation.Binary.Bundles.DecPreorder.preorder
d_preorder_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> T_Preorder_142
d_preorder_412 ~v0 ~v1 ~v2 v3 = du_preorder_412 v3
du_preorder_412 :: T_DecPreorder_342 -> T_Preorder_142
du_preorder_412 v0
  = coe
      C_constructor_232
      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_194
         (coe d_isDecPreorder_364 (coe v0)))
-- Relation.Binary.Bundles.DecPreorder._._∼_
d__'8764'__416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> AgdaAny -> AgdaAny -> ()
d__'8764'__416 = erased
-- Relation.Binary.Bundles.DecPreorder._._≉_
d__'8777'__418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> AgdaAny -> AgdaAny -> ()
d__'8777'__418 = erased
-- Relation.Binary.Bundles.DecPreorder._._∼ᵒ_
d__'8764''7506'__420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__420 = erased
-- Relation.Binary.Bundles.DecPreorder._._≁_
d__'8769'__422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> AgdaAny -> AgdaAny -> ()
d__'8769'__422 = erased
-- Relation.Binary.Bundles.DecPreorder._._≁ᵒ_
d__'8769''7506'__424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__424 = erased
-- Relation.Binary.Bundles.DecPreorder._.isEquivalence
d_isEquivalence_426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_426 ~v0 ~v1 ~v2 v3 = du_isEquivalence_426 v3
du_isEquivalence_426 ::
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_426 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_194
         (coe d_isDecPreorder_364 (coe v0)))
-- Relation.Binary.Bundles.DecPreorder._.rawRelation
d_rawRelation_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_428 = erased
-- Relation.Binary.Bundles.DecPreorder._.rawSetoid
d_rawSetoid_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_430 = erased
-- Relation.Binary.Bundles.DecPreorder._.refl
d_refl_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> AgdaAny -> AgdaAny
d_refl_432 ~v0 ~v1 ~v2 v3 = du_refl_432 v3
du_refl_432 :: T_DecPreorder_342 -> AgdaAny -> AgdaAny
du_refl_432 v0
  = let v1 = coe du_preorder_412 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.DecPreorder._.reflexive
d_reflexive_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_434 ~v0 ~v1 ~v2 v3 = du_reflexive_434 v3
du_reflexive_434 ::
  T_DecPreorder_342 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_434 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_194
         (coe d_isDecPreorder_364 (coe v0)))
-- Relation.Binary.Bundles.DecPreorder._.trans
d_trans_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_436 ~v0 ~v1 ~v2 v3 = du_trans_436 v3
du_trans_436 ::
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_436 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_194
         (coe d_isDecPreorder_364 (coe v0)))
-- Relation.Binary.Bundles.DecPreorder._.∼-resp-≈
d_'8764''45'resp'45''8776'_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_438 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_438 v3
du_'8764''45'resp'45''8776'_438 ::
  T_DecPreorder_342 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_438 v0
  = let v1 = coe du_preorder_412 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.DecPreorder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_440 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_440 v3
du_'8764''45'resp'691''45''8776'_440 ::
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_440 v0
  = let v1 = coe du_preorder_412 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.DecPreorder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_442 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_442 v3
du_'8764''45'resp'737''45''8776'_442 ::
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_442 v0
  = let v1 = coe du_preorder_412 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.DecPreorder._.≲-resp-≈
d_'8818''45'resp'45''8776'_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_444 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_444 v3
du_'8818''45'resp'45''8776'_444 ::
  T_DecPreorder_342 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_444 v0
  = let v1 = coe du_preorder_412 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.DecPreorder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_446 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_446 v3
du_'8818''45'resp'691''45''8776'_446 ::
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_446 v0
  = let v1 = coe du_preorder_412 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.DecPreorder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_448 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_448 v3
du_'8818''45'resp'737''45''8776'_448 ::
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_448 v0
  = let v1 = coe du_preorder_412 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.DecPreorder.Eq.decSetoid
d_decSetoid_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> T_DecSetoid_90
d_decSetoid_452 ~v0 ~v1 ~v2 v3 = du_decSetoid_452 v3
du_decSetoid_452 :: T_DecPreorder_342 -> T_DecSetoid_90
du_decSetoid_452 v0
  = coe
      C_constructor_134
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_224
         (coe d_isDecPreorder_364 (coe v0)))
-- Relation.Binary.Bundles.DecPreorder.Eq._._≈_
d__'8776'__456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> AgdaAny -> AgdaAny -> ()
d__'8776'__456 = erased
-- Relation.Binary.Bundles.DecPreorder.Eq._._≉_
d__'8777'__458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> AgdaAny -> AgdaAny -> ()
d__'8777'__458 = erased
-- Relation.Binary.Bundles.DecPreorder.Eq._._≟_
d__'8799'__460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__460 ~v0 ~v1 ~v2 v3 = du__'8799'__460 v3
du__'8799'__460 ::
  T_DecPreorder_342 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__460 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__196
      (coe d_isDecPreorder_364 (coe v0))
-- Relation.Binary.Bundles.DecPreorder.Eq._.Carrier
d_Carrier_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_DecPreorder_342 -> ()
d_Carrier_462 = erased
-- Relation.Binary.Bundles.DecPreorder.Eq._.isDecEquivalence
d_isDecEquivalence_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_464 ~v0 ~v1 ~v2 v3 = du_isDecEquivalence_464 v3
du_isDecEquivalence_464 ::
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_464 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_224
      (coe d_isDecPreorder_364 (coe v0))
-- Relation.Binary.Bundles.DecPreorder.Eq._.isEquivalence
d_isEquivalence_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_466 ~v0 ~v1 ~v2 v3 = du_isEquivalence_466 v3
du_isEquivalence_466 ::
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_466 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_194
         (coe d_isDecPreorder_364 (coe v0)))
-- Relation.Binary.Bundles.DecPreorder.Eq._.isPartialEquivalence
d_isPartialEquivalence_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_468 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_468 v3
du_isPartialEquivalence_468 ::
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_468 v0
  = let v1 = coe du_decSetoid_452 (coe v0) in
    coe
      (let v2 = coe du_setoid_114 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.DecPreorder.Eq._.partialSetoid
d_partialSetoid_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> T_PartialSetoid_10
d_partialSetoid_470 ~v0 ~v1 ~v2 v3 = du_partialSetoid_470 v3
du_partialSetoid_470 :: T_DecPreorder_342 -> T_PartialSetoid_10
du_partialSetoid_470 v0
  = let v1 = coe du_decSetoid_452 (coe v0) in
    coe (coe du_partialSetoid_72 (coe du_setoid_114 (coe v1)))
-- Relation.Binary.Bundles.DecPreorder.Eq._.rawSetoid
d_rawSetoid_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_472 = erased
-- Relation.Binary.Bundles.DecPreorder.Eq._.refl
d_refl_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> AgdaAny -> AgdaAny
d_refl_474 ~v0 ~v1 ~v2 v3 = du_refl_474 v3
du_refl_474 :: T_DecPreorder_342 -> AgdaAny -> AgdaAny
du_refl_474 v0
  = let v1 = coe du_decSetoid_452 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
            (coe d_isDecEquivalence_106 (coe v1))))
-- Relation.Binary.Bundles.DecPreorder.Eq._.reflexive
d_reflexive_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_476 ~v0 ~v1 ~v2 v3 = du_reflexive_476 v3
du_reflexive_476 ::
  T_DecPreorder_342 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_476 v0
  = let v1 = coe du_decSetoid_452 (coe v0) in
    coe
      (let v2 = coe du_setoid_114 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe d_isEquivalence_62 (coe v2)) v3))
-- Relation.Binary.Bundles.DecPreorder.Eq._.setoid
d_setoid_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> T_Setoid_46
d_setoid_478 ~v0 ~v1 ~v2 v3 = du_setoid_478 v3
du_setoid_478 :: T_DecPreorder_342 -> T_Setoid_46
du_setoid_478 v0
  = coe du_setoid_114 (coe du_decSetoid_452 (coe v0))
-- Relation.Binary.Bundles.DecPreorder.Eq._.sym
d_sym_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_480 ~v0 ~v1 ~v2 v3 = du_sym_480 v3
du_sym_480 ::
  T_DecPreorder_342 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_480 v0
  = let v1 = coe du_decSetoid_452 (coe v0) in
    coe
      (let v2 = coe du_setoid_114 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.DecPreorder.Eq._.trans
d_trans_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_482 ~v0 ~v1 ~v2 v3 = du_trans_482 v3
du_trans_482 ::
  T_DecPreorder_342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_482 v0
  = let v1 = coe du_decSetoid_452 (coe v0) in
    coe
      (let v2 = coe du_setoid_114 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.Poset
d_Poset_492 a0 a1 a2 = ()
newtype T_Poset_492
  = C_constructor_588 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
-- Relation.Binary.Bundles.Poset.Carrier
d_Carrier_508 :: T_Poset_492 -> ()
d_Carrier_508 = erased
-- Relation.Binary.Bundles.Poset._≈_
d__'8776'__510 :: T_Poset_492 -> AgdaAny -> AgdaAny -> ()
d__'8776'__510 = erased
-- Relation.Binary.Bundles.Poset._≤_
d__'8804'__512 :: T_Poset_492 -> AgdaAny -> AgdaAny -> ()
d__'8804'__512 = erased
-- Relation.Binary.Bundles.Poset.isPartialOrder
d_isPartialOrder_514 ::
  T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_514 v0
  = case coe v0 of
      C_constructor_588 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.Poset._.antisym
d_antisym_518 ::
  T_Poset_492 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_518 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe d_isPartialOrder_514 (coe v0))
-- Relation.Binary.Bundles.Poset._.isPreorder
d_isPreorder_520 ::
  T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_520 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe d_isPartialOrder_514 (coe v0))
-- Relation.Binary.Bundles.Poset.preorder
d_preorder_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> T_Preorder_142
d_preorder_522 ~v0 ~v1 ~v2 v3 = du_preorder_522 v3
du_preorder_522 :: T_Poset_492 -> T_Preorder_142
du_preorder_522 v0
  = coe
      C_constructor_232
      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_514 (coe v0)))
-- Relation.Binary.Bundles.Poset._._∼_
d__'8764'__526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> AgdaAny -> AgdaAny -> ()
d__'8764'__526 = erased
-- Relation.Binary.Bundles.Poset._._≉_
d__'8777'__528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> AgdaAny -> AgdaAny -> ()
d__'8777'__528 = erased
-- Relation.Binary.Bundles.Poset._.isEquivalence
d_isEquivalence_530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_530 ~v0 ~v1 ~v2 v3 = du_isEquivalence_530 v3
du_isEquivalence_530 ::
  T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_530 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_514 (coe v0)))
-- Relation.Binary.Bundles.Poset._.rawRelation
d_rawRelation_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_532 = erased
-- Relation.Binary.Bundles.Poset._.rawSetoid
d_rawSetoid_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_534 = erased
-- Relation.Binary.Bundles.Poset._.refl
d_refl_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> AgdaAny -> AgdaAny
d_refl_536 ~v0 ~v1 ~v2 v3 = du_refl_536 v3
du_refl_536 :: T_Poset_492 -> AgdaAny -> AgdaAny
du_refl_536 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.Poset._.reflexive
d_reflexive_538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_538 ~v0 ~v1 ~v2 v3 = du_reflexive_538 v3
du_reflexive_538 ::
  T_Poset_492 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_538 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_514 (coe v0)))
-- Relation.Binary.Bundles.Poset._.trans
d_trans_540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_540 ~v0 ~v1 ~v2 v3 = du_trans_540 v3
du_trans_540 ::
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_540 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_514 (coe v0)))
-- Relation.Binary.Bundles.Poset._.∼-resp-≈
d_'8764''45'resp'45''8776'_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_542 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_542 v3
du_'8764''45'resp'45''8776'_542 ::
  T_Poset_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_542 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.Poset._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_544 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_544 v3
du_'8764''45'resp'691''45''8776'_544 ::
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_544 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.Poset._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_546 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_546 v3
du_'8764''45'resp'737''45''8776'_546 ::
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_546 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.Poset._.≲-resp-≈
d_'8818''45'resp'45''8776'_548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_548 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_548 v3
du_'8818''45'resp'45''8776'_548 ::
  T_Poset_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_548 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.Poset._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_550 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_550 v3
du_'8818''45'resp'691''45''8776'_550 ::
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_550 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.Poset._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_552 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_552 v3
du_'8818''45'resp'737''45''8776'_552 ::
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_552 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.Poset._.Eq._≈_
d__'8776'__556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> AgdaAny -> AgdaAny -> ()
d__'8776'__556 = erased
-- Relation.Binary.Bundles.Poset._.Eq._≉_
d__'8777'__558 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> AgdaAny -> AgdaAny -> ()
d__'8777'__558 = erased
-- Relation.Binary.Bundles.Poset._.Eq.Carrier
d_Carrier_560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_Poset_492 -> ()
d_Carrier_560 = erased
-- Relation.Binary.Bundles.Poset._.Eq.isEquivalence
d_isEquivalence_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_562 ~v0 ~v1 ~v2 v3 = du_isEquivalence_562 v3
du_isEquivalence_562 ::
  T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_562 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe d_isPreorder_164 (coe v1)))
-- Relation.Binary.Bundles.Poset._.Eq.isPartialEquivalence
d_isPartialEquivalence_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_564 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_564 v3
du_isPartialEquivalence_564 ::
  T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_564 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (let v2 = coe du_setoid_190 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.Poset._.Eq.partialSetoid
d_partialSetoid_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> T_PartialSetoid_10
d_partialSetoid_566 ~v0 ~v1 ~v2 v3 = du_partialSetoid_566 v3
du_partialSetoid_566 :: T_Poset_492 -> T_PartialSetoid_10
du_partialSetoid_566 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe (coe du_partialSetoid_72 (coe du_setoid_190 (coe v1)))
-- Relation.Binary.Bundles.Poset._.Eq.rawSetoid
d_rawSetoid_568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_568 = erased
-- Relation.Binary.Bundles.Poset._.Eq.refl
d_refl_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> AgdaAny -> AgdaAny
d_refl_570 ~v0 ~v1 ~v2 v3 = du_refl_570 v3
du_refl_570 :: T_Poset_492 -> AgdaAny -> AgdaAny
du_refl_570 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe d_isPreorder_164 (coe v1))))
-- Relation.Binary.Bundles.Poset._.Eq.reflexive
d_reflexive_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_572 ~v0 ~v1 ~v2 v3 = du_reflexive_572 v3
du_reflexive_572 ::
  T_Poset_492 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_572 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (let v2 = coe du_setoid_190 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe d_isEquivalence_62 (coe v2)) v3))
-- Relation.Binary.Bundles.Poset._.Eq.setoid
d_setoid_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> T_Setoid_46
d_setoid_574 ~v0 ~v1 ~v2 v3 = du_setoid_574 v3
du_setoid_574 :: T_Poset_492 -> T_Setoid_46
du_setoid_574 v0 = coe du_setoid_190 (coe du_preorder_522 (coe v0))
-- Relation.Binary.Bundles.Poset._.Eq.sym
d_sym_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_576 ~v0 ~v1 ~v2 v3 = du_sym_576 v3
du_sym_576 ::
  T_Poset_492 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_576 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (let v2 = coe du_setoid_190 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.Poset._.Eq.trans
d_trans_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_578 ~v0 ~v1 ~v2 v3 = du_trans_578 v3
du_trans_578 ::
  T_Poset_492 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_578 v0
  = let v1 = coe du_preorder_522 (coe v0) in
    coe
      (let v2 = coe du_setoid_190 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.Poset._._∼ᵒ_
d__'8764''7506'__582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__582 = erased
-- Relation.Binary.Bundles.Poset._._≁_
d__'8769'__584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> AgdaAny -> AgdaAny -> ()
d__'8769'__584 = erased
-- Relation.Binary.Bundles.Poset._._≁ᵒ_
d__'8769''7506'__586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_492 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__586 = erased
-- Relation.Binary.Bundles.DecPoset
d_DecPoset_596 a0 a1 a2 = ()
newtype T_DecPoset_596
  = C_constructor_752 MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
-- Relation.Binary.Bundles.DecPoset.Carrier
d_Carrier_612 :: T_DecPoset_596 -> ()
d_Carrier_612 = erased
-- Relation.Binary.Bundles.DecPoset._≈_
d__'8776'__614 :: T_DecPoset_596 -> AgdaAny -> AgdaAny -> ()
d__'8776'__614 = erased
-- Relation.Binary.Bundles.DecPoset._≤_
d__'8804'__616 :: T_DecPoset_596 -> AgdaAny -> AgdaAny -> ()
d__'8804'__616 = erased
-- Relation.Binary.Bundles.DecPoset.isDecPartialOrder
d_isDecPartialOrder_618 ::
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
d_isDecPartialOrder_618 v0
  = case coe v0 of
      C_constructor_752 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.DecPoset.DPO._≟_
d__'8799'__622 ::
  T_DecPoset_596 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__622 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__312
      (coe d_isDecPartialOrder_618 (coe v0))
-- Relation.Binary.Bundles.DecPoset.DPO._≤?_
d__'8804''63'__624 ::
  T_DecPoset_596 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__624 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__314
      (coe d_isDecPartialOrder_618 (coe v0))
-- Relation.Binary.Bundles.DecPoset.DPO.isDecPreorder
d_isDecPreorder_628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPreorder_184
d_isDecPreorder_628 ~v0 ~v1 ~v2 v3 = du_isDecPreorder_628 v3
du_isDecPreorder_628 ::
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPreorder_184
du_isDecPreorder_628 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isDecPreorder_342
      (coe d_isDecPartialOrder_618 (coe v0))
-- Relation.Binary.Bundles.DecPoset.DPO.isPartialOrder
d_isPartialOrder_632 ::
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_632 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_310
      (coe d_isDecPartialOrder_618 (coe v0))
-- Relation.Binary.Bundles.DecPoset.poset
d_poset_672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> T_Poset_492
d_poset_672 ~v0 ~v1 ~v2 v3 = du_poset_672 v3
du_poset_672 :: T_DecPoset_596 -> T_Poset_492
du_poset_672 v0
  = coe
      C_constructor_588
      (MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_310
         (coe d_isDecPartialOrder_618 (coe v0)))
-- Relation.Binary.Bundles.DecPoset._._∼_
d__'8764'__676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> AgdaAny -> AgdaAny -> ()
d__'8764'__676 = erased
-- Relation.Binary.Bundles.DecPoset._._≉_
d__'8777'__678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> AgdaAny -> AgdaAny -> ()
d__'8777'__678 = erased
-- Relation.Binary.Bundles.DecPoset._._∼ᵒ_
d__'8764''7506'__680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__680 = erased
-- Relation.Binary.Bundles.DecPoset._._≁_
d__'8769'__682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> AgdaAny -> AgdaAny -> ()
d__'8769'__682 = erased
-- Relation.Binary.Bundles.DecPoset._._≁ᵒ_
d__'8769''7506'__684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__684 = erased
-- Relation.Binary.Bundles.DecPoset._.antisym
d_antisym_686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_686 ~v0 ~v1 ~v2 v3 = du_antisym_686 v3
du_antisym_686 ::
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_686 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_310
         (coe d_isDecPartialOrder_618 (coe v0)))
-- Relation.Binary.Bundles.DecPoset._.isEquivalence
d_isEquivalence_688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_688 ~v0 ~v1 ~v2 v3 = du_isEquivalence_688 v3
du_isEquivalence_688 ::
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_688 v0
  = let v1 = coe du_poset_672 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_514 (coe v1))))
-- Relation.Binary.Bundles.DecPoset._.isPreorder
d_isPreorder_690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_690 ~v0 ~v1 ~v2 v3 = du_isPreorder_690 v3
du_isPreorder_690 ::
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_690 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_310
         (coe d_isDecPartialOrder_618 (coe v0)))
-- Relation.Binary.Bundles.DecPoset._.preorder
d_preorder_692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> T_Preorder_142
d_preorder_692 ~v0 ~v1 ~v2 v3 = du_preorder_692 v3
du_preorder_692 :: T_DecPoset_596 -> T_Preorder_142
du_preorder_692 v0
  = coe du_preorder_522 (coe du_poset_672 (coe v0))
-- Relation.Binary.Bundles.DecPoset._.rawRelation
d_rawRelation_694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_694 = erased
-- Relation.Binary.Bundles.DecPoset._.rawSetoid
d_rawSetoid_696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_696 = erased
-- Relation.Binary.Bundles.DecPoset._.refl
d_refl_698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> AgdaAny -> AgdaAny
d_refl_698 ~v0 ~v1 ~v2 v3 = du_refl_698 v3
du_refl_698 :: T_DecPoset_596 -> AgdaAny -> AgdaAny
du_refl_698 v0
  = let v1 = coe du_poset_672 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.reflexive
d_reflexive_700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_700 ~v0 ~v1 ~v2 v3 = du_reflexive_700 v3
du_reflexive_700 ::
  T_DecPoset_596 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_700 v0
  = let v1 = coe du_poset_672 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_514 (coe v1))))
-- Relation.Binary.Bundles.DecPoset._.trans
d_trans_702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_702 ~v0 ~v1 ~v2 v3 = du_trans_702 v3
du_trans_702 ::
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_702 v0
  = let v1 = coe du_poset_672 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_90
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_514 (coe v1))))
-- Relation.Binary.Bundles.DecPoset._.∼-resp-≈
d_'8764''45'resp'45''8776'_704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_704 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_704 v3
du_'8764''45'resp'45''8776'_704 ::
  T_DecPoset_596 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_704 v0
  = let v1 = coe du_poset_672 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_706 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_706 v3
du_'8764''45'resp'691''45''8776'_706 ::
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_706 v0
  = let v1 = coe du_poset_672 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_708 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_708 v3
du_'8764''45'resp'737''45''8776'_708 ::
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_708 v0
  = let v1 = coe du_poset_672 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.≲-resp-≈
d_'8818''45'resp'45''8776'_710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_710 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_710 v3
du_'8818''45'resp'45''8776'_710 ::
  T_DecPoset_596 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_710 v0
  = let v1 = coe du_poset_672 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_712 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_712 v3
du_'8818''45'resp'691''45''8776'_712 ::
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_712 v0
  = let v1 = coe du_poset_672 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_714 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_714 v3
du_'8818''45'resp'737''45''8776'_714 ::
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_714 v0
  = let v1 = coe du_poset_672 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.DecPoset.decPreorder
d_decPreorder_716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> T_DecPreorder_342
d_decPreorder_716 ~v0 ~v1 ~v2 v3 = du_decPreorder_716 v3
du_decPreorder_716 :: T_DecPoset_596 -> T_DecPreorder_342
du_decPreorder_716 v0
  = coe
      C_constructor_484
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecPreorder_342
         (coe d_isDecPartialOrder_618 (coe v0)))
-- Relation.Binary.Bundles.DecPoset._.Eq._≈_
d__'8776'__722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> AgdaAny -> AgdaAny -> ()
d__'8776'__722 = erased
-- Relation.Binary.Bundles.DecPoset._.Eq._≉_
d__'8777'__724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> AgdaAny -> AgdaAny -> ()
d__'8777'__724 = erased
-- Relation.Binary.Bundles.DecPoset._.Eq._≟_
d__'8799'__726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__726 ~v0 ~v1 ~v2 v3 = du__'8799'__726 v3
du__'8799'__726 ::
  T_DecPoset_596 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__726 v0
  = let v1 = coe du_decPreorder_716 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__196
         (coe d_isDecPreorder_364 (coe v1)))
-- Relation.Binary.Bundles.DecPoset._.Eq.Carrier
d_Carrier_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_DecPoset_596 -> ()
d_Carrier_728 = erased
-- Relation.Binary.Bundles.DecPoset._.Eq.decSetoid
d_decSetoid_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> T_DecSetoid_90
d_decSetoid_730 ~v0 ~v1 ~v2 v3 = du_decSetoid_730 v3
du_decSetoid_730 :: T_DecPoset_596 -> T_DecSetoid_90
du_decSetoid_730 v0
  = coe du_decSetoid_452 (coe du_decPreorder_716 (coe v0))
-- Relation.Binary.Bundles.DecPoset._.Eq.isDecEquivalence
d_isDecEquivalence_732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_732 ~v0 ~v1 ~v2 v3 = du_isDecEquivalence_732 v3
du_isDecEquivalence_732 ::
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_732 v0
  = let v1 = coe du_decPreorder_716 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_224
         (coe d_isDecPreorder_364 (coe v1)))
-- Relation.Binary.Bundles.DecPoset._.Eq.isEquivalence
d_isEquivalence_734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_734 ~v0 ~v1 ~v2 v3 = du_isEquivalence_734 v3
du_isEquivalence_734 ::
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_734 v0
  = let v1 = coe du_decPreorder_716 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_194
            (coe d_isDecPreorder_364 (coe v1))))
-- Relation.Binary.Bundles.DecPoset._.Eq.isPartialEquivalence
d_isPartialEquivalence_736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_736 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_736 v3
du_isPartialEquivalence_736 ::
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_736 v0
  = let v1 = coe du_decPreorder_716 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_452 (coe v1) in
       coe
         (let v3 = coe du_setoid_114 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_62 (coe v3)))))
-- Relation.Binary.Bundles.DecPoset._.Eq.partialSetoid
d_partialSetoid_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> T_PartialSetoid_10
d_partialSetoid_738 ~v0 ~v1 ~v2 v3 = du_partialSetoid_738 v3
du_partialSetoid_738 :: T_DecPoset_596 -> T_PartialSetoid_10
du_partialSetoid_738 v0
  = let v1 = coe du_decPreorder_716 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_452 (coe v1) in
       coe (coe du_partialSetoid_72 (coe du_setoid_114 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.Eq.rawSetoid
d_rawSetoid_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_740 = erased
-- Relation.Binary.Bundles.DecPoset._.Eq.refl
d_refl_742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> AgdaAny -> AgdaAny
d_refl_742 ~v0 ~v1 ~v2 v3 = du_refl_742 v3
du_refl_742 :: T_DecPoset_596 -> AgdaAny -> AgdaAny
du_refl_742 v0
  = let v1 = coe du_decPreorder_716 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_452 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
               (coe d_isDecEquivalence_106 (coe v2)))))
-- Relation.Binary.Bundles.DecPoset._.Eq.reflexive
d_reflexive_744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_744 ~v0 ~v1 ~v2 v3 = du_reflexive_744 v3
du_reflexive_744 ::
  T_DecPoset_596 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_744 v0
  = let v1 = coe du_decPreorder_716 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_452 (coe v1) in
       coe
         (let v3 = coe du_setoid_114 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_62 (coe v3)) v4)))
-- Relation.Binary.Bundles.DecPoset._.Eq.setoid
d_setoid_746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> T_Setoid_46
d_setoid_746 ~v0 ~v1 ~v2 v3 = du_setoid_746 v3
du_setoid_746 :: T_DecPoset_596 -> T_Setoid_46
du_setoid_746 v0
  = let v1 = coe du_decPreorder_716 (coe v0) in
    coe (coe du_setoid_114 (coe du_decSetoid_452 (coe v1)))
-- Relation.Binary.Bundles.DecPoset._.Eq.sym
d_sym_748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_748 ~v0 ~v1 ~v2 v3 = du_sym_748 v3
du_sym_748 ::
  T_DecPoset_596 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_748 v0
  = let v1 = coe du_decPreorder_716 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_452 (coe v1) in
       coe
         (let v3 = coe du_setoid_114 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe d_isEquivalence_62 (coe v3)))))
-- Relation.Binary.Bundles.DecPoset._.Eq.trans
d_trans_750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_750 ~v0 ~v1 ~v2 v3 = du_trans_750 v3
du_trans_750 ::
  T_DecPoset_596 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_750 v0
  = let v1 = coe du_decPreorder_716 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_452 (coe v1) in
       coe
         (let v3 = coe du_setoid_114 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe d_isEquivalence_62 (coe v3)))))
-- Relation.Binary.Bundles.StrictPartialOrder
d_StrictPartialOrder_760 a0 a1 a2 = ()
newtype T_StrictPartialOrder_760
  = C_constructor_842 MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
-- Relation.Binary.Bundles.StrictPartialOrder.Carrier
d_Carrier_776 :: T_StrictPartialOrder_760 -> ()
d_Carrier_776 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._≈_
d__'8776'__778 ::
  T_StrictPartialOrder_760 -> AgdaAny -> AgdaAny -> ()
d__'8776'__778 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._<_
d__'60'__780 ::
  T_StrictPartialOrder_760 -> AgdaAny -> AgdaAny -> ()
d__'60'__780 = erased
-- Relation.Binary.Bundles.StrictPartialOrder.isStrictPartialOrder
d_isStrictPartialOrder_782 ::
  T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_isStrictPartialOrder_782 v0
  = case coe v0 of
      C_constructor_842 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.StrictPartialOrder._.<-resp-≈
d_'60''45'resp'45''8776'_786 ::
  T_StrictPartialOrder_760 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_786 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
      (coe d_isStrictPartialOrder_782 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_788 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_788 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_788 v3
du_'60''45'resp'691''45''8776'_788 ::
  T_StrictPartialOrder_760 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_788 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_408
      (coe d_isStrictPartialOrder_782 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_790 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_790 v3
du_'60''45'resp'737''45''8776'_790 ::
  T_StrictPartialOrder_760 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_790 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_410
      (coe d_isStrictPartialOrder_782 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder._.asym
d_asym_792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_792 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._.irrefl
d_irrefl_794 ::
  T_StrictPartialOrder_760 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_794 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._.isEquivalence
d_isEquivalence_796 ::
  T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_796 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
      (coe d_isStrictPartialOrder_782 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder._.trans
d_trans_798 ::
  T_StrictPartialOrder_760 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_798 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_386
      (coe d_isStrictPartialOrder_782 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq.setoid
d_setoid_802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 -> T_Setoid_46
d_setoid_802 ~v0 ~v1 ~v2 v3 = du_setoid_802 v3
du_setoid_802 :: T_StrictPartialOrder_760 -> T_Setoid_46
du_setoid_802 v0
  = coe
      C_constructor_84
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
         (coe d_isStrictPartialOrder_782 (coe v0)))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._._≈_
d__'8776'__806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 -> AgdaAny -> AgdaAny -> ()
d__'8776'__806 = erased
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._._≉_
d__'8777'__808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 -> AgdaAny -> AgdaAny -> ()
d__'8777'__808 = erased
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.Carrier
d_Carrier_810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 -> ()
d_Carrier_810 = erased
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.isEquivalence
d_isEquivalence_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_812 ~v0 ~v1 ~v2 v3 = du_isEquivalence_812 v3
du_isEquivalence_812 ::
  T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_812 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
      (coe d_isStrictPartialOrder_782 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.isPartialEquivalence
d_isPartialEquivalence_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_814 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_814 v3
du_isPartialEquivalence_814 ::
  T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_814 v0
  = let v1 = coe du_setoid_802 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_62 (coe v1)))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.partialSetoid
d_partialSetoid_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 -> T_PartialSetoid_10
d_partialSetoid_816 ~v0 ~v1 ~v2 v3 = du_partialSetoid_816 v3
du_partialSetoid_816 ::
  T_StrictPartialOrder_760 -> T_PartialSetoid_10
du_partialSetoid_816 v0
  = coe du_partialSetoid_72 (coe du_setoid_802 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.rawSetoid
d_rawSetoid_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_818 = erased
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.refl
d_refl_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 -> AgdaAny -> AgdaAny
d_refl_820 ~v0 ~v1 ~v2 v3 = du_refl_820 v3
du_refl_820 :: T_StrictPartialOrder_760 -> AgdaAny -> AgdaAny
du_refl_820 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
         (coe d_isStrictPartialOrder_782 (coe v0)))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.reflexive
d_reflexive_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_822 ~v0 ~v1 ~v2 v3 = du_reflexive_822 v3
du_reflexive_822 ::
  T_StrictPartialOrder_760 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_822 v0
  = let v1 = coe du_setoid_802 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_62 (coe v1)) v2)
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.sym
d_sym_824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_824 ~v0 ~v1 ~v2 v3 = du_sym_824 v3
du_sym_824 ::
  T_StrictPartialOrder_760 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_824 v0
  = let v1 = coe du_setoid_802 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe d_isEquivalence_62 (coe v1)))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.trans
d_trans_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_826 ~v0 ~v1 ~v2 v3 = du_trans_826 v3
du_trans_826 ::
  T_StrictPartialOrder_760 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_826 v0
  = let v1 = coe du_setoid_802 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe d_isEquivalence_62 (coe v1)))
-- Relation.Binary.Bundles.StrictPartialOrder.rawRelation
d_rawRelation_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_828 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._._∼ᵒ_
d__'8764''7506'__832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__832 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._._≉_
d__'8777'__834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 -> AgdaAny -> AgdaAny -> ()
d__'8777'__834 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._._≁_
d__'8769'__836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 -> AgdaAny -> AgdaAny -> ()
d__'8769'__836 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._._≁ᵒ_
d__'8769''7506'__838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__838 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._.rawSetoid
d_rawSetoid_840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_840 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder
d_DecStrictPartialOrder_850 a0 a1 a2 = ()
newtype T_DecStrictPartialOrder_850
  = C_constructor_978 MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
-- Relation.Binary.Bundles.DecStrictPartialOrder.Carrier
d_Carrier_866 :: T_DecStrictPartialOrder_850 -> ()
d_Carrier_866 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._≈_
d__'8776'__868 ::
  T_DecStrictPartialOrder_850 -> AgdaAny -> AgdaAny -> ()
d__'8776'__868 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._<_
d__'60'__870 ::
  T_DecStrictPartialOrder_850 -> AgdaAny -> AgdaAny -> ()
d__'60'__870 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder.isDecStrictPartialOrder
d_isDecStrictPartialOrder_872 ::
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
d_isDecStrictPartialOrder_872 v0
  = case coe v0 of
      C_constructor_978 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.DecStrictPartialOrder.DSPO._<?_
d__'60''63'__876 ::
  T_DecStrictPartialOrder_850 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__876 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'60''63'__432
      (coe d_isDecStrictPartialOrder_872 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.DSPO._≟_
d__'8799'__878 ::
  T_DecStrictPartialOrder_850 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__878 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__430
      (coe d_isDecStrictPartialOrder_872 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.DSPO.isStrictPartialOrder
d_isStrictPartialOrder_892 ::
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_isStrictPartialOrder_892 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_428
      (coe d_isDecStrictPartialOrder_872 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.strictPartialOrder
d_strictPartialOrder_914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> T_StrictPartialOrder_760
d_strictPartialOrder_914 ~v0 ~v1 ~v2 v3
  = du_strictPartialOrder_914 v3
du_strictPartialOrder_914 ::
  T_DecStrictPartialOrder_850 -> T_StrictPartialOrder_760
du_strictPartialOrder_914 v0
  = coe
      C_constructor_842
      (MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_428
         (coe d_isDecStrictPartialOrder_872 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder._._∼ᵒ_
d__'8764''7506'__918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__918 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._._≉_
d__'8777'__920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> AgdaAny -> AgdaAny -> ()
d__'8777'__920 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._._≁_
d__'8769'__922 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> AgdaAny -> AgdaAny -> ()
d__'8769'__922 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._._≁ᵒ_
d__'8769''7506'__924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__924 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._.<-resp-≈
d_'60''45'resp'45''8776'_926 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_926 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_926 v3
du_'60''45'resp'45''8776'_926 ::
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_926 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_428
         (coe d_isDecStrictPartialOrder_872 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_928 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_928 v3
du_'60''45'resp'691''45''8776'_928 ::
  T_DecStrictPartialOrder_850 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_928 v0
  = let v1 = coe du_strictPartialOrder_914 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_408
         (coe d_isStrictPartialOrder_782 (coe v1)))
-- Relation.Binary.Bundles.DecStrictPartialOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_930 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_930 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_930 v3
du_'60''45'resp'737''45''8776'_930 ::
  T_DecStrictPartialOrder_850 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_930 v0
  = let v1 = coe du_strictPartialOrder_914 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_410
         (coe d_isStrictPartialOrder_782 (coe v1)))
-- Relation.Binary.Bundles.DecStrictPartialOrder._.asym
d_asym_932 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_932 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._.irrefl
d_irrefl_934 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_934 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._.isEquivalence
d_isEquivalence_936 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_936 ~v0 ~v1 ~v2 v3 = du_isEquivalence_936 v3
du_isEquivalence_936 ::
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_936 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_428
         (coe d_isDecStrictPartialOrder_872 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder._.rawRelation
d_rawRelation_938 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_938 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._.rawSetoid
d_rawSetoid_940 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_940 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._.trans
d_trans_942 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_942 ~v0 ~v1 ~v2 v3 = du_trans_942 v3
du_trans_942 ::
  T_DecStrictPartialOrder_850 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_942 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_386
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_428
         (coe d_isDecStrictPartialOrder_872 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq.decSetoid
d_decSetoid_946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> T_DecSetoid_90
d_decSetoid_946 ~v0 ~v1 ~v2 v3 = du_decSetoid_946 v3
du_decSetoid_946 :: T_DecStrictPartialOrder_850 -> T_DecSetoid_90
du_decSetoid_946 v0
  = coe
      C_constructor_134
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_464
         (coe d_isDecStrictPartialOrder_872 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._._≈_
d__'8776'__950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> AgdaAny -> AgdaAny -> ()
d__'8776'__950 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._._≉_
d__'8777'__952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> AgdaAny -> AgdaAny -> ()
d__'8777'__952 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._._≟_
d__'8799'__954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__954 ~v0 ~v1 ~v2 v3 = du__'8799'__954 v3
du__'8799'__954 ::
  T_DecStrictPartialOrder_850 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__954 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__430
      (coe d_isDecStrictPartialOrder_872 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.Carrier
d_Carrier_956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> ()
d_Carrier_956 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.isDecEquivalence
d_isDecEquivalence_958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_958 ~v0 ~v1 ~v2 v3 = du_isDecEquivalence_958 v3
du_isDecEquivalence_958 ::
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_958 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_464
      (coe d_isDecStrictPartialOrder_872 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.isEquivalence
d_isEquivalence_960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_960 ~v0 ~v1 ~v2 v3 = du_isEquivalence_960 v3
du_isEquivalence_960 ::
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_960 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_428
         (coe d_isDecStrictPartialOrder_872 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.isPartialEquivalence
d_isPartialEquivalence_962 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_962 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_962 v3
du_isPartialEquivalence_962 ::
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_962 v0
  = let v1 = coe du_decSetoid_946 (coe v0) in
    coe
      (let v2 = coe du_setoid_114 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.partialSetoid
d_partialSetoid_964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> T_PartialSetoid_10
d_partialSetoid_964 ~v0 ~v1 ~v2 v3 = du_partialSetoid_964 v3
du_partialSetoid_964 ::
  T_DecStrictPartialOrder_850 -> T_PartialSetoid_10
du_partialSetoid_964 v0
  = let v1 = coe du_decSetoid_946 (coe v0) in
    coe (coe du_partialSetoid_72 (coe du_setoid_114 (coe v1)))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.rawSetoid
d_rawSetoid_966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_966 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.refl
d_refl_968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> AgdaAny -> AgdaAny
d_refl_968 ~v0 ~v1 ~v2 v3 = du_refl_968 v3
du_refl_968 :: T_DecStrictPartialOrder_850 -> AgdaAny -> AgdaAny
du_refl_968 v0
  = let v1 = coe du_decSetoid_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
            (coe d_isDecEquivalence_106 (coe v1))))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.reflexive
d_reflexive_970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_970 ~v0 ~v1 ~v2 v3 = du_reflexive_970 v3
du_reflexive_970 ::
  T_DecStrictPartialOrder_850 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_970 v0
  = let v1 = coe du_decSetoid_946 (coe v0) in
    coe
      (let v2 = coe du_setoid_114 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe d_isEquivalence_62 (coe v2)) v3))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.setoid
d_setoid_972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 -> T_Setoid_46
d_setoid_972 ~v0 ~v1 ~v2 v3 = du_setoid_972 v3
du_setoid_972 :: T_DecStrictPartialOrder_850 -> T_Setoid_46
du_setoid_972 v0
  = coe du_setoid_114 (coe du_decSetoid_946 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.sym
d_sym_974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_974 ~v0 ~v1 ~v2 v3 = du_sym_974 v3
du_sym_974 ::
  T_DecStrictPartialOrder_850 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_974 v0
  = let v1 = coe du_decSetoid_946 (coe v0) in
    coe
      (let v2 = coe du_setoid_114 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.trans
d_trans_976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_850 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_976 ~v0 ~v1 ~v2 v3 = du_trans_976 v3
du_trans_976 ::
  T_DecStrictPartialOrder_850 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_976 v0
  = let v1 = coe du_decSetoid_946 (coe v0) in
    coe
      (let v2 = coe du_setoid_114 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe d_isEquivalence_62 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder
d_TotalOrder_986 a0 a1 a2 = ()
newtype T_TotalOrder_986
  = C_constructor_1090 MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
-- Relation.Binary.Bundles.TotalOrder.Carrier
d_Carrier_1002 :: T_TotalOrder_986 -> ()
d_Carrier_1002 = erased
-- Relation.Binary.Bundles.TotalOrder._≈_
d__'8776'__1004 :: T_TotalOrder_986 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1004 = erased
-- Relation.Binary.Bundles.TotalOrder._≤_
d__'8804'__1006 :: T_TotalOrder_986 -> AgdaAny -> AgdaAny -> ()
d__'8804'__1006 = erased
-- Relation.Binary.Bundles.TotalOrder.isTotalOrder
d_isTotalOrder_1008 ::
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_isTotalOrder_1008 v0
  = case coe v0 of
      C_constructor_1090 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.TotalOrder._.isPartialOrder
d_isPartialOrder_1012 ::
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_1012 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
      (coe d_isTotalOrder_1008 (coe v0))
-- Relation.Binary.Bundles.TotalOrder._.isTotalPreorder
d_isTotalPreorder_1014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132
d_isTotalPreorder_1014 ~v0 ~v1 ~v2 v3 = du_isTotalPreorder_1014 v3
du_isTotalPreorder_1014 ::
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132
du_isTotalPreorder_1014 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isTotalPreorder_538
      (coe d_isTotalOrder_1008 (coe v0))
-- Relation.Binary.Bundles.TotalOrder._.total
d_total_1016 ::
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_1016 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_total_498
      (coe d_isTotalOrder_1008 (coe v0))
-- Relation.Binary.Bundles.TotalOrder.poset
d_poset_1018 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> T_Poset_492
d_poset_1018 ~v0 ~v1 ~v2 v3 = du_poset_1018 v3
du_poset_1018 :: T_TotalOrder_986 -> T_Poset_492
du_poset_1018 v0
  = coe
      C_constructor_588
      (MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
         (coe d_isTotalOrder_1008 (coe v0)))
-- Relation.Binary.Bundles.TotalOrder._._∼_
d__'8764'__1022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> AgdaAny -> AgdaAny -> ()
d__'8764'__1022 = erased
-- Relation.Binary.Bundles.TotalOrder._._≉_
d__'8777'__1024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1024 = erased
-- Relation.Binary.Bundles.TotalOrder._._∼ᵒ_
d__'8764''7506'__1026 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__1026 = erased
-- Relation.Binary.Bundles.TotalOrder._._≁_
d__'8769'__1028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> AgdaAny -> AgdaAny -> ()
d__'8769'__1028 = erased
-- Relation.Binary.Bundles.TotalOrder._._≁ᵒ_
d__'8769''7506'__1030 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__1030 = erased
-- Relation.Binary.Bundles.TotalOrder._.antisym
d_antisym_1032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_1032 ~v0 ~v1 ~v2 v3 = du_antisym_1032 v3
du_antisym_1032 ::
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_1032 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
         (coe d_isTotalOrder_1008 (coe v0)))
-- Relation.Binary.Bundles.TotalOrder._.isEquivalence
d_isEquivalence_1034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1034 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1034 v3
du_isEquivalence_1034 ::
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1034 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_514 (coe v1))))
-- Relation.Binary.Bundles.TotalOrder._.isPreorder
d_isPreorder_1036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_1036 ~v0 ~v1 ~v2 v3 = du_isPreorder_1036 v3
du_isPreorder_1036 ::
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_1036 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
         (coe d_isTotalOrder_1008 (coe v0)))
-- Relation.Binary.Bundles.TotalOrder._.preorder
d_preorder_1038 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> T_Preorder_142
d_preorder_1038 ~v0 ~v1 ~v2 v3 = du_preorder_1038 v3
du_preorder_1038 :: T_TotalOrder_986 -> T_Preorder_142
du_preorder_1038 v0
  = coe du_preorder_522 (coe du_poset_1018 (coe v0))
-- Relation.Binary.Bundles.TotalOrder._.rawRelation
d_rawRelation_1040 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_1040 = erased
-- Relation.Binary.Bundles.TotalOrder._.rawSetoid
d_rawSetoid_1042 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1042 = erased
-- Relation.Binary.Bundles.TotalOrder._.refl
d_refl_1044 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> AgdaAny -> AgdaAny
d_refl_1044 ~v0 ~v1 ~v2 v3 = du_refl_1044 v3
du_refl_1044 :: T_TotalOrder_986 -> AgdaAny -> AgdaAny
du_refl_1044 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.reflexive
d_reflexive_1046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_1046 ~v0 ~v1 ~v2 v3 = du_reflexive_1046 v3
du_reflexive_1046 ::
  T_TotalOrder_986 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_1046 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_514 (coe v1))))
-- Relation.Binary.Bundles.TotalOrder._.trans
d_trans_1048 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1048 ~v0 ~v1 ~v2 v3 = du_trans_1048 v3
du_trans_1048 ::
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1048 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_90
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_514 (coe v1))))
-- Relation.Binary.Bundles.TotalOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_1050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_1050 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_1050 v3
du_'8764''45'resp'45''8776'_1050 ::
  T_TotalOrder_986 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_1050 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_1052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_1052 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_1052 v3
du_'8764''45'resp'691''45''8776'_1052 ::
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_1052 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_1054 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_1054 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_1054 v3
du_'8764''45'resp'737''45''8776'_1054 ::
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_1054 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_1056 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_1056 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_1056 v3
du_'8818''45'resp'45''8776'_1056 ::
  T_TotalOrder_986 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_1056 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_1058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_1058 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_1058 v3
du_'8818''45'resp'691''45''8776'_1058 ::
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_1058 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_1060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_1060 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_1060 v3
du_'8818''45'resp'737''45''8776'_1060 ::
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_1060 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.Eq._≈_
d__'8776'__1064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1064 = erased
-- Relation.Binary.Bundles.TotalOrder._.Eq._≉_
d__'8777'__1066 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1066 = erased
-- Relation.Binary.Bundles.TotalOrder._.Eq.Carrier
d_Carrier_1068 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_TotalOrder_986 -> ()
d_Carrier_1068 = erased
-- Relation.Binary.Bundles.TotalOrder._.Eq.isEquivalence
d_isEquivalence_1070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1070 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1070 v3
du_isEquivalence_1070 ::
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1070 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe d_isPreorder_164 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_1072 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1072 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1072 v3
du_isPartialEquivalence_1072 ::
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1072 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (let v3 = coe du_setoid_190 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_62 (coe v3)))))
-- Relation.Binary.Bundles.TotalOrder._.Eq.partialSetoid
d_partialSetoid_1074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> T_PartialSetoid_10
d_partialSetoid_1074 ~v0 ~v1 ~v2 v3 = du_partialSetoid_1074 v3
du_partialSetoid_1074 :: T_TotalOrder_986 -> T_PartialSetoid_10
du_partialSetoid_1074 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe (coe du_partialSetoid_72 (coe du_setoid_190 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.Eq.rawSetoid
d_rawSetoid_1076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1076 = erased
-- Relation.Binary.Bundles.TotalOrder._.Eq.refl
d_refl_1078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> AgdaAny -> AgdaAny
d_refl_1078 ~v0 ~v1 ~v2 v3 = du_refl_1078 v3
du_refl_1078 :: T_TotalOrder_986 -> AgdaAny -> AgdaAny
du_refl_1078 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
               (coe d_isPreorder_164 (coe v2)))))
-- Relation.Binary.Bundles.TotalOrder._.Eq.reflexive
d_reflexive_1080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1080 ~v0 ~v1 ~v2 v3 = du_reflexive_1080 v3
du_reflexive_1080 ::
  T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1080 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (let v3 = coe du_setoid_190 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_62 (coe v3)) v4)))
-- Relation.Binary.Bundles.TotalOrder._.Eq.setoid
d_setoid_1082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> T_Setoid_46
d_setoid_1082 ~v0 ~v1 ~v2 v3 = du_setoid_1082 v3
du_setoid_1082 :: T_TotalOrder_986 -> T_Setoid_46
du_setoid_1082 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe (coe du_setoid_190 (coe du_preorder_522 (coe v1)))
-- Relation.Binary.Bundles.TotalOrder._.Eq.sym
d_sym_1084 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1084 ~v0 ~v1 ~v2 v3 = du_sym_1084 v3
du_sym_1084 ::
  T_TotalOrder_986 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1084 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (let v3 = coe du_setoid_190 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe d_isEquivalence_62 (coe v3)))))
-- Relation.Binary.Bundles.TotalOrder._.Eq.trans
d_trans_1086 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1086 ~v0 ~v1 ~v2 v3 = du_trans_1086 v3
du_trans_1086 ::
  T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1086 v0
  = let v1 = coe du_poset_1018 (coe v0) in
    coe
      (let v2 = coe du_preorder_522 (coe v1) in
       coe
         (let v3 = coe du_setoid_190 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe d_isEquivalence_62 (coe v3)))))
-- Relation.Binary.Bundles.TotalOrder.totalPreorder
d_totalPreorder_1088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_986 -> T_TotalPreorder_240
d_totalPreorder_1088 ~v0 ~v1 ~v2 v3 = du_totalPreorder_1088 v3
du_totalPreorder_1088 :: T_TotalOrder_986 -> T_TotalPreorder_240
du_totalPreorder_1088 v0
  = coe
      C_constructor_334
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isTotalPreorder_538
         (coe d_isTotalOrder_1008 (coe v0)))
-- Relation.Binary.Bundles.DecTotalOrder
d_DecTotalOrder_1098 a0 a1 a2 = ()
newtype T_DecTotalOrder_1098
  = C_constructor_1272 MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
-- Relation.Binary.Bundles.DecTotalOrder.Carrier
d_Carrier_1114 :: T_DecTotalOrder_1098 -> ()
d_Carrier_1114 = erased
-- Relation.Binary.Bundles.DecTotalOrder._≈_
d__'8776'__1116 :: T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1116 = erased
-- Relation.Binary.Bundles.DecTotalOrder._≤_
d__'8804'__1118 :: T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> ()
d__'8804'__1118 = erased
-- Relation.Binary.Bundles.DecTotalOrder.isDecTotalOrder
d_isDecTotalOrder_1120 ::
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_isDecTotalOrder_1120 v0
  = case coe v0 of
      C_constructor_1272 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.DecTotalOrder.DTO._≟_
d__'8799'__1124 ::
  T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__1124 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__558
      (coe d_isDecTotalOrder_1120 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder.DTO._≤?_
d__'8804''63'__1126 ::
  T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__1126 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__560
      (coe d_isDecTotalOrder_1120 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder.DTO.isDecPartialOrder
d_isDecPartialOrder_1130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
d_isDecPartialOrder_1130 ~v0 ~v1 ~v2 v3
  = du_isDecPartialOrder_1130 v3
du_isDecPartialOrder_1130 ::
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
du_isDecPartialOrder_1130 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isDecPartialOrder_594
      (coe d_isDecTotalOrder_1120 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder.DTO.isTotalOrder
d_isTotalOrder_1140 ::
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_isTotalOrder_1140 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
      (coe d_isDecTotalOrder_1120 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder.totalOrder
d_totalOrder_1182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> T_TotalOrder_986
d_totalOrder_1182 ~v0 ~v1 ~v2 v3 = du_totalOrder_1182 v3
du_totalOrder_1182 :: T_DecTotalOrder_1098 -> T_TotalOrder_986
du_totalOrder_1182 v0
  = coe
      C_constructor_1090
      (MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
         (coe d_isDecTotalOrder_1120 (coe v0)))
-- Relation.Binary.Bundles.DecTotalOrder._._∼_
d__'8764'__1186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> ()
d__'8764'__1186 = erased
-- Relation.Binary.Bundles.DecTotalOrder._._≉_
d__'8777'__1188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1188 = erased
-- Relation.Binary.Bundles.DecTotalOrder._._∼ᵒ_
d__'8764''7506'__1190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__1190 = erased
-- Relation.Binary.Bundles.DecTotalOrder._._≁_
d__'8769'__1192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> ()
d__'8769'__1192 = erased
-- Relation.Binary.Bundles.DecTotalOrder._._≁ᵒ_
d__'8769''7506'__1194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__1194 = erased
-- Relation.Binary.Bundles.DecTotalOrder._.antisym
d_antisym_1196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_1196 ~v0 ~v1 ~v2 v3 = du_antisym_1196 v3
du_antisym_1196 ::
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_1196 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
            (coe d_isTotalOrder_1008 (coe v1))))
-- Relation.Binary.Bundles.DecTotalOrder._.isEquivalence
d_isEquivalence_1198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1198 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1198 v3
du_isEquivalence_1198 ::
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1198 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (let v2 = coe du_poset_1018 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe d_isPartialOrder_514 (coe v2)))))
-- Relation.Binary.Bundles.DecTotalOrder._.isPartialOrder
d_isPartialOrder_1200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_1200 ~v0 ~v1 ~v2 v3 = du_isPartialOrder_1200 v3
du_isPartialOrder_1200 ::
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_isPartialOrder_1200 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
         (coe d_isDecTotalOrder_1120 (coe v0)))
-- Relation.Binary.Bundles.DecTotalOrder._.isPreorder
d_isPreorder_1202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_1202 ~v0 ~v1 ~v2 v3 = du_isPreorder_1202 v3
du_isPreorder_1202 ::
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_1202 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
            (coe d_isTotalOrder_1008 (coe v1))))
-- Relation.Binary.Bundles.DecTotalOrder._.isTotalPreorder
d_isTotalPreorder_1204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132
d_isTotalPreorder_1204 ~v0 ~v1 ~v2 v3 = du_isTotalPreorder_1204 v3
du_isTotalPreorder_1204 ::
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132
du_isTotalPreorder_1204 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isTotalPreorder_538
         (coe d_isTotalOrder_1008 (coe v1)))
-- Relation.Binary.Bundles.DecTotalOrder._.poset
d_poset_1206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> T_Poset_492
d_poset_1206 ~v0 ~v1 ~v2 v3 = du_poset_1206 v3
du_poset_1206 :: T_DecTotalOrder_1098 -> T_Poset_492
du_poset_1206 v0
  = coe du_poset_1018 (coe du_totalOrder_1182 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder._.preorder
d_preorder_1208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> T_Preorder_142
d_preorder_1208 ~v0 ~v1 ~v2 v3 = du_preorder_1208 v3
du_preorder_1208 :: T_DecTotalOrder_1098 -> T_Preorder_142
du_preorder_1208 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe (coe du_preorder_522 (coe du_poset_1018 (coe v1)))
-- Relation.Binary.Bundles.DecTotalOrder._.rawRelation
d_rawRelation_1210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_1210 = erased
-- Relation.Binary.Bundles.DecTotalOrder._.rawSetoid
d_rawSetoid_1212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1212 = erased
-- Relation.Binary.Bundles.DecTotalOrder._.refl
d_refl_1214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny
d_refl_1214 ~v0 ~v1 ~v2 v3 = du_refl_1214 v3
du_refl_1214 :: T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny
du_refl_1214 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (let v2 = coe du_poset_1018 (coe v1) in
       coe
         (let v3 = coe du_preorder_522 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_104
               (coe d_isPreorder_164 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.reflexive
d_reflexive_1216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_1216 ~v0 ~v1 ~v2 v3 = du_reflexive_1216 v3
du_reflexive_1216 ::
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_1216 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (let v2 = coe du_poset_1018 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe d_isPartialOrder_514 (coe v2)))))
-- Relation.Binary.Bundles.DecTotalOrder._.total
d_total_1218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_1218 ~v0 ~v1 ~v2 v3 = du_total_1218 v3
du_total_1218 ::
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_total_1218 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_total_498
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
         (coe d_isDecTotalOrder_1120 (coe v0)))
-- Relation.Binary.Bundles.DecTotalOrder._.totalPreorder
d_totalPreorder_1220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> T_TotalPreorder_240
d_totalPreorder_1220 ~v0 ~v1 ~v2 v3 = du_totalPreorder_1220 v3
du_totalPreorder_1220 ::
  T_DecTotalOrder_1098 -> T_TotalPreorder_240
du_totalPreorder_1220 v0
  = coe du_totalPreorder_1088 (coe du_totalOrder_1182 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder._.trans
d_trans_1222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1222 ~v0 ~v1 ~v2 v3 = du_trans_1222 v3
du_trans_1222 ::
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1222 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (let v2 = coe du_poset_1018 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_90
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe d_isPartialOrder_514 (coe v2)))))
-- Relation.Binary.Bundles.DecTotalOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_1224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_1224 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_1224 v3
du_'8764''45'resp'45''8776'_1224 ::
  T_DecTotalOrder_1098 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_1224 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (let v2 = coe du_poset_1018 (coe v1) in
       coe
         (let v3 = coe du_preorder_522 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
               (coe d_isPreorder_164 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_1226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_1226 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_1226 v3
du_'8764''45'resp'691''45''8776'_1226 ::
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_1226 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (let v2 = coe du_poset_1018 (coe v1) in
       coe
         (let v3 = coe du_preorder_522 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
               (coe d_isPreorder_164 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_1228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_1228 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_1228 v3
du_'8764''45'resp'737''45''8776'_1228 ::
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_1228 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (let v2 = coe du_poset_1018 (coe v1) in
       coe
         (let v3 = coe du_preorder_522 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
               (coe d_isPreorder_164 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_1230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_1230 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_1230 v3
du_'8818''45'resp'45''8776'_1230 ::
  T_DecTotalOrder_1098 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_1230 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (let v2 = coe du_poset_1018 (coe v1) in
       coe
         (let v3 = coe du_preorder_522 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
               (coe d_isPreorder_164 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_1232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_1232 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_1232 v3
du_'8818''45'resp'691''45''8776'_1232 ::
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_1232 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (let v2 = coe du_poset_1018 (coe v1) in
       coe
         (let v3 = coe du_preorder_522 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
               (coe d_isPreorder_164 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_1234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_1234 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_1234 v3
du_'8818''45'resp'737''45''8776'_1234 ::
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_1234 v0
  = let v1 = coe du_totalOrder_1182 (coe v0) in
    coe
      (let v2 = coe du_poset_1018 (coe v1) in
       coe
         (let v3 = coe du_preorder_522 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
               (coe d_isPreorder_164 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder.decPoset
d_decPoset_1236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> T_DecPoset_596
d_decPoset_1236 ~v0 ~v1 ~v2 v3 = du_decPoset_1236 v3
du_decPoset_1236 :: T_DecTotalOrder_1098 -> T_DecPoset_596
du_decPoset_1236 v0
  = coe
      C_constructor_752
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecPartialOrder_594
         (coe d_isDecTotalOrder_1120 (coe v0)))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq._≈_
d__'8776'__1242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1242 = erased
-- Relation.Binary.Bundles.DecTotalOrder._.Eq._≉_
d__'8777'__1244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1244 = erased
-- Relation.Binary.Bundles.DecTotalOrder._.Eq._≟_
d__'8799'__1246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__1246 ~v0 ~v1 ~v2 v3 = du__'8799'__1246 v3
du__'8799'__1246 ::
  T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__1246 v0
  = let v1 = coe du_decPoset_1236 (coe v0) in
    coe
      (let v2 = coe du_decPreorder_716 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__196
            (coe d_isDecPreorder_364 (coe v2))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.Carrier
d_Carrier_1248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> ()
d_Carrier_1248 = erased
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.decSetoid
d_decSetoid_1250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> T_DecSetoid_90
d_decSetoid_1250 ~v0 ~v1 ~v2 v3 = du_decSetoid_1250 v3
du_decSetoid_1250 :: T_DecTotalOrder_1098 -> T_DecSetoid_90
du_decSetoid_1250 v0
  = let v1 = coe du_decPoset_1236 (coe v0) in
    coe (coe du_decSetoid_452 (coe du_decPreorder_716 (coe v1)))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.isDecEquivalence
d_isDecEquivalence_1252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_1252 ~v0 ~v1 ~v2 v3
  = du_isDecEquivalence_1252 v3
du_isDecEquivalence_1252 ::
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_1252 v0
  = let v1 = coe du_decPoset_1236 (coe v0) in
    coe
      (let v2 = coe du_decPreorder_716 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_224
            (coe d_isDecPreorder_364 (coe v2))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.isEquivalence
d_isEquivalence_1254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1254 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1254 v3
du_isEquivalence_1254 ::
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1254 v0
  = let v1 = coe du_decPoset_1236 (coe v0) in
    coe
      (let v2 = coe du_decPreorder_716 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_194
               (coe d_isDecPreorder_364 (coe v2)))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_1256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1256 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1256 v3
du_isPartialEquivalence_1256 ::
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1256 v0
  = let v1 = coe du_decPoset_1236 (coe v0) in
    coe
      (let v2 = coe du_decPreorder_716 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_452 (coe v2) in
          coe
            (let v4 = coe du_setoid_114 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe d_isEquivalence_62 (coe v4))))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.partialSetoid
d_partialSetoid_1258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> T_PartialSetoid_10
d_partialSetoid_1258 ~v0 ~v1 ~v2 v3 = du_partialSetoid_1258 v3
du_partialSetoid_1258 :: T_DecTotalOrder_1098 -> T_PartialSetoid_10
du_partialSetoid_1258 v0
  = let v1 = coe du_decPoset_1236 (coe v0) in
    coe
      (let v2 = coe du_decPreorder_716 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_452 (coe v2) in
          coe (coe du_partialSetoid_72 (coe du_setoid_114 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.rawSetoid
d_rawSetoid_1260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1260 = erased
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.refl
d_refl_1262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny
d_refl_1262 ~v0 ~v1 ~v2 v3 = du_refl_1262 v3
du_refl_1262 :: T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny
du_refl_1262 v0
  = let v1 = coe du_decPoset_1236 (coe v0) in
    coe
      (let v2 = coe du_decPreorder_716 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_452 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_36
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
                  (coe d_isDecEquivalence_106 (coe v3))))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.reflexive
d_reflexive_1264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1264 ~v0 ~v1 ~v2 v3 = du_reflexive_1264 v3
du_reflexive_1264 ::
  T_DecTotalOrder_1098 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1264 v0
  = let v1 = coe du_decPoset_1236 (coe v0) in
    coe
      (let v2 = coe du_decPreorder_716 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_452 (coe v2) in
          coe
            (let v4 = coe du_setoid_114 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe d_isEquivalence_62 (coe v4)) v5))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.setoid
d_setoid_1266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> T_Setoid_46
d_setoid_1266 ~v0 ~v1 ~v2 v3 = du_setoid_1266 v3
du_setoid_1266 :: T_DecTotalOrder_1098 -> T_Setoid_46
du_setoid_1266 v0
  = let v1 = coe du_decPoset_1236 (coe v0) in
    coe
      (let v2 = coe du_decPreorder_716 (coe v1) in
       coe (coe du_setoid_114 (coe du_decSetoid_452 (coe v2))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.sym
d_sym_1268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1268 ~v0 ~v1 ~v2 v3 = du_sym_1268 v3
du_sym_1268 ::
  T_DecTotalOrder_1098 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1268 v0
  = let v1 = coe du_decPoset_1236 (coe v0) in
    coe
      (let v2 = coe du_decPreorder_716 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_452 (coe v2) in
          coe
            (let v4 = coe du_setoid_114 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe d_isEquivalence_62 (coe v4))))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.trans
d_trans_1270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1270 ~v0 ~v1 ~v2 v3 = du_trans_1270 v3
du_trans_1270 ::
  T_DecTotalOrder_1098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1270 v0
  = let v1 = coe du_decPoset_1236 (coe v0) in
    coe
      (let v2 = coe du_decPreorder_716 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_452 (coe v2) in
          coe
            (let v4 = coe du_setoid_114 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe d_isEquivalence_62 (coe v4))))))
-- Relation.Binary.Bundles.StrictTotalOrder
d_StrictTotalOrder_1280 a0 a1 a2 = ()
newtype T_StrictTotalOrder_1280
  = C_constructor_1386 MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
-- Relation.Binary.Bundles.StrictTotalOrder.Carrier
d_Carrier_1296 :: T_StrictTotalOrder_1280 -> ()
d_Carrier_1296 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._≈_
d__'8776'__1298 ::
  T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1298 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._<_
d__'60'__1300 ::
  T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny -> ()
d__'60'__1300 = erased
-- Relation.Binary.Bundles.StrictTotalOrder.isStrictTotalOrder
d_isStrictTotalOrder_1302 ::
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_isStrictTotalOrder_1302 v0
  = case coe v0 of
      C_constructor_1386 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.StrictTotalOrder._._<?_
d__'60''63'__1306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__1306 ~v0 ~v1 ~v2 v3 = du__'60''63'__1306 v3
du__'60''63'__1306 ::
  T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'60''63'__1306 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du__'60''63'__654
      (coe d_isStrictTotalOrder_1302 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._._≟_
d__'8799'__1308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__1308 ~v0 ~v1 ~v2 v3 = du__'8799'__1308 v3
du__'8799'__1308 ::
  T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__1308 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du__'8799'__652
      (coe d_isStrictTotalOrder_1302 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._.compare
d_compare_1310 ::
  T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_1310 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_compare_634
      (coe d_isStrictTotalOrder_1302 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._.isDecEquivalence
d_isDecEquivalence_1312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_1312 ~v0 ~v1 ~v2 v3
  = du_isDecEquivalence_1312 v3
du_isDecEquivalence_1312 ::
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_1312 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_678
      (coe d_isStrictTotalOrder_1302 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._.isDecStrictPartialOrder
d_isDecStrictPartialOrder_1314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
d_isDecStrictPartialOrder_1314 ~v0 ~v1 ~v2 v3
  = du_isDecStrictPartialOrder_1314 v3
du_isDecStrictPartialOrder_1314 ::
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
du_isDecStrictPartialOrder_1314 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isDecStrictPartialOrder_656
      (coe d_isStrictTotalOrder_1302 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._.isStrictPartialOrder
d_isStrictPartialOrder_1316 ::
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_isStrictPartialOrder_1316 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
      (coe d_isStrictTotalOrder_1302 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder.strictPartialOrder
d_strictPartialOrder_1318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> T_StrictPartialOrder_760
d_strictPartialOrder_1318 ~v0 ~v1 ~v2 v3
  = du_strictPartialOrder_1318 v3
du_strictPartialOrder_1318 ::
  T_StrictTotalOrder_1280 -> T_StrictPartialOrder_760
du_strictPartialOrder_1318 v0
  = coe
      C_constructor_842
      (MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
         (coe d_isStrictTotalOrder_1302 (coe v0)))
-- Relation.Binary.Bundles.StrictTotalOrder._._∼ᵒ_
d__'8764''7506'__1322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__1322 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._._≉_
d__'8777'__1324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1324 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._._≁_
d__'8769'__1326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny -> ()
d__'8769'__1326 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._._≁ᵒ_
d__'8769''7506'__1328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__1328 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.<-resp-≈
d_'60''45'resp'45''8776'_1330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_1330 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_1330 v3
du_'60''45'resp'45''8776'_1330 ::
  T_StrictTotalOrder_1280 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_1330 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
         (coe d_isStrictTotalOrder_1302 (coe v0)))
-- Relation.Binary.Bundles.StrictTotalOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_1332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_1332 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_1332 v3
du_'60''45'resp'691''45''8776'_1332 ::
  T_StrictTotalOrder_1280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_1332 v0
  = let v1 = coe du_strictPartialOrder_1318 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_408
         (coe d_isStrictPartialOrder_782 (coe v1)))
-- Relation.Binary.Bundles.StrictTotalOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_1334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_1334 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_1334 v3
du_'60''45'resp'737''45''8776'_1334 ::
  T_StrictTotalOrder_1280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_1334 v0
  = let v1 = coe du_strictPartialOrder_1318 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_410
         (coe d_isStrictPartialOrder_782 (coe v1)))
-- Relation.Binary.Bundles.StrictTotalOrder._.asym
d_asym_1336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_1336 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.irrefl
d_irrefl_1338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_1338 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.isEquivalence
d_isEquivalence_1340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1340 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1340 v3
du_isEquivalence_1340 ::
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1340 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
         (coe d_isStrictTotalOrder_1302 (coe v0)))
-- Relation.Binary.Bundles.StrictTotalOrder._.rawRelation
d_rawRelation_1342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_1342 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.rawSetoid
d_rawSetoid_1344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1344 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.trans
d_trans_1346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1346 ~v0 ~v1 ~v2 v3 = du_trans_1346 v3
du_trans_1346 ::
  T_StrictTotalOrder_1280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1346 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_386
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
         (coe d_isStrictTotalOrder_1302 (coe v0)))
-- Relation.Binary.Bundles.StrictTotalOrder.decStrictPartialOrder
d_decStrictPartialOrder_1348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> T_DecStrictPartialOrder_850
d_decStrictPartialOrder_1348 ~v0 ~v1 ~v2 v3
  = du_decStrictPartialOrder_1348 v3
du_decStrictPartialOrder_1348 ::
  T_StrictTotalOrder_1280 -> T_DecStrictPartialOrder_850
du_decStrictPartialOrder_1348 v0
  = coe
      C_constructor_978
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecStrictPartialOrder_656
         (coe d_isStrictTotalOrder_1302 (coe v0)))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq._≈_
d__'8776'__1354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1354 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq._≉_
d__'8777'__1356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1356 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq._≟_
d__'8799'__1358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__1358 ~v0 ~v1 ~v2 v3 = du__'8799'__1358 v3
du__'8799'__1358 ::
  T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__1358 v0
  = let v1 = coe du_decStrictPartialOrder_1348 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__430
         (coe d_isDecStrictPartialOrder_872 (coe v1)))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.Carrier
d_Carrier_1360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> ()
d_Carrier_1360 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.decSetoid
d_decSetoid_1362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> T_DecSetoid_90
d_decSetoid_1362 ~v0 ~v1 ~v2 v3 = du_decSetoid_1362 v3
du_decSetoid_1362 :: T_StrictTotalOrder_1280 -> T_DecSetoid_90
du_decSetoid_1362 v0
  = coe du_decSetoid_946 (coe du_decStrictPartialOrder_1348 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.isDecEquivalence
d_isDecEquivalence_1364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_1364 ~v0 ~v1 ~v2 v3
  = du_isDecEquivalence_1364 v3
du_isDecEquivalence_1364 ::
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_1364 v0
  = let v1 = coe du_decStrictPartialOrder_1348 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_464
         (coe d_isDecStrictPartialOrder_872 (coe v1)))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.isEquivalence
d_isEquivalence_1366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1366 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1366 v3
du_isEquivalence_1366 ::
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1366 v0
  = let v1 = coe du_decStrictPartialOrder_1348 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_428
            (coe d_isDecStrictPartialOrder_872 (coe v1))))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_1368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1368 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1368 v3
du_isPartialEquivalence_1368 ::
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1368 v0
  = let v1 = coe du_decStrictPartialOrder_1348 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_946 (coe v1) in
       coe
         (let v3 = coe du_setoid_114 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_isEquivalence_62 (coe v3)))))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.partialSetoid
d_partialSetoid_1370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> T_PartialSetoid_10
d_partialSetoid_1370 ~v0 ~v1 ~v2 v3 = du_partialSetoid_1370 v3
du_partialSetoid_1370 ::
  T_StrictTotalOrder_1280 -> T_PartialSetoid_10
du_partialSetoid_1370 v0
  = let v1 = coe du_decStrictPartialOrder_1348 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_946 (coe v1) in
       coe (coe du_partialSetoid_72 (coe du_setoid_114 (coe v2))))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.rawSetoid
d_rawSetoid_1372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1372 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.refl
d_refl_1374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny
d_refl_1374 ~v0 ~v1 ~v2 v3 = du_refl_1374 v3
du_refl_1374 :: T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny
du_refl_1374 v0
  = let v1 = coe du_decStrictPartialOrder_1348 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_946 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
               (coe d_isDecEquivalence_106 (coe v2)))))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.reflexive
d_reflexive_1376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1376 ~v0 ~v1 ~v2 v3 = du_reflexive_1376 v3
du_reflexive_1376 ::
  T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1376 v0
  = let v1 = coe du_decStrictPartialOrder_1348 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_946 (coe v1) in
       coe
         (let v3 = coe du_setoid_114 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_isEquivalence_62 (coe v3)) v4)))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.setoid
d_setoid_1378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> T_Setoid_46
d_setoid_1378 ~v0 ~v1 ~v2 v3 = du_setoid_1378 v3
du_setoid_1378 :: T_StrictTotalOrder_1280 -> T_Setoid_46
du_setoid_1378 v0
  = let v1 = coe du_decStrictPartialOrder_1348 (coe v0) in
    coe (coe du_setoid_114 (coe du_decSetoid_946 (coe v1)))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.sym
d_sym_1380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1380 ~v0 ~v1 ~v2 v3 = du_sym_1380 v3
du_sym_1380 ::
  T_StrictTotalOrder_1280 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1380 v0
  = let v1 = coe du_decStrictPartialOrder_1348 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_946 (coe v1) in
       coe
         (let v3 = coe du_setoid_114 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe d_isEquivalence_62 (coe v3)))))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.trans
d_trans_1382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1382 ~v0 ~v1 ~v2 v3 = du_trans_1382 v3
du_trans_1382 ::
  T_StrictTotalOrder_1280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1382 v0
  = let v1 = coe du_decStrictPartialOrder_1348 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_946 (coe v1) in
       coe
         (let v3 = coe du_setoid_114 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe d_isEquivalence_62 (coe v3)))))
-- Relation.Binary.Bundles.StrictTotalOrder.decSetoid
d_decSetoid_1384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1280 -> T_DecSetoid_90
d_decSetoid_1384 ~v0 ~v1 ~v2 v3 = du_decSetoid_1384 v3
du_decSetoid_1384 :: T_StrictTotalOrder_1280 -> T_DecSetoid_90
du_decSetoid_1384 v0
  = coe du_decSetoid_946 (coe du_decStrictPartialOrder_1348 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder
d_DenseLinearOrder_1394 a0 a1 a2 = ()
newtype T_DenseLinearOrder_1394
  = C_constructor_1504 MAlonzo.Code.Relation.Binary.Structures.T_IsDenseLinearOrder_686
-- Relation.Binary.Bundles.DenseLinearOrder.Carrier
d_Carrier_1410 :: T_DenseLinearOrder_1394 -> ()
d_Carrier_1410 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._≈_
d__'8776'__1412 ::
  T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1412 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._<_
d__'60'__1414 ::
  T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny -> ()
d__'60'__1414 = erased
-- Relation.Binary.Bundles.DenseLinearOrder.isDenseLinearOrder
d_isDenseLinearOrder_1416 ::
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDenseLinearOrder_686
d_isDenseLinearOrder_1416 v0
  = case coe v0 of
      C_constructor_1504 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.DenseLinearOrder._.dense
d_dense_1420 ::
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dense_1420 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_dense_696
      (coe d_isDenseLinearOrder_1416 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder._.isStrictTotalOrder
d_isStrictTotalOrder_1422 ::
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_isStrictTotalOrder_1422 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isStrictTotalOrder_694
      (coe d_isDenseLinearOrder_1416 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder.strictTotalOrder
d_strictTotalOrder_1424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> T_StrictTotalOrder_1280
d_strictTotalOrder_1424 ~v0 ~v1 ~v2 v3
  = du_strictTotalOrder_1424 v3
du_strictTotalOrder_1424 ::
  T_DenseLinearOrder_1394 -> T_StrictTotalOrder_1280
du_strictTotalOrder_1424 v0
  = coe
      C_constructor_1386
      (MAlonzo.Code.Relation.Binary.Structures.d_isStrictTotalOrder_694
         (coe d_isDenseLinearOrder_1416 (coe v0)))
-- Relation.Binary.Bundles.DenseLinearOrder._._<?_
d__'60''63'__1428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__1428 ~v0 ~v1 ~v2 v3 = du__'60''63'__1428 v3
du__'60''63'__1428 ::
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'60''63'__1428 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du__'60''63'__654
         (coe d_isStrictTotalOrder_1302 (coe v1)))
-- Relation.Binary.Bundles.DenseLinearOrder._._∼ᵒ_
d__'8764''7506'__1430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__1430 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._._≉_
d__'8777'__1432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1432 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._._≟_
d__'8799'__1434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__1434 ~v0 ~v1 ~v2 v3 = du__'8799'__1434 v3
du__'8799'__1434 ::
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__1434 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du__'8799'__652
         (coe d_isStrictTotalOrder_1302 (coe v1)))
-- Relation.Binary.Bundles.DenseLinearOrder._._≁_
d__'8769'__1436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny -> ()
d__'8769'__1436 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._._≁ᵒ_
d__'8769''7506'__1438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__1438 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.<-resp-≈
d_'60''45'resp'45''8776'_1440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_1440 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_1440 v3
du_'60''45'resp'45''8776'_1440 ::
  T_DenseLinearOrder_1394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_1440 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe d_isStrictTotalOrder_1302 (coe v1))))
-- Relation.Binary.Bundles.DenseLinearOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_1442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_1442 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_1442 v3
du_'60''45'resp'691''45''8776'_1442 ::
  T_DenseLinearOrder_1394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_1442 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_strictPartialOrder_1318 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_408
            (coe d_isStrictPartialOrder_782 (coe v2))))
-- Relation.Binary.Bundles.DenseLinearOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_1444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_1444 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_1444 v3
du_'60''45'resp'737''45''8776'_1444 ::
  T_DenseLinearOrder_1394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_1444 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_strictPartialOrder_1318 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_410
            (coe d_isStrictPartialOrder_782 (coe v2))))
-- Relation.Binary.Bundles.DenseLinearOrder._.asym
d_asym_1446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_1446 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.compare
d_compare_1448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_1448 ~v0 ~v1 ~v2 v3 = du_compare_1448 v3
du_compare_1448 ::
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_compare_1448 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_compare_634
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictTotalOrder_694
         (coe d_isDenseLinearOrder_1416 (coe v0)))
-- Relation.Binary.Bundles.DenseLinearOrder._.decSetoid
d_decSetoid_1450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> T_DecSetoid_90
d_decSetoid_1450 ~v0 ~v1 ~v2 v3 = du_decSetoid_1450 v3
du_decSetoid_1450 :: T_DenseLinearOrder_1394 -> T_DecSetoid_90
du_decSetoid_1450 v0
  = coe du_decSetoid_1384 (coe du_strictTotalOrder_1424 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder._.decStrictPartialOrder
d_decStrictPartialOrder_1452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> T_DecStrictPartialOrder_850
d_decStrictPartialOrder_1452 ~v0 ~v1 ~v2 v3
  = du_decStrictPartialOrder_1452 v3
du_decStrictPartialOrder_1452 ::
  T_DenseLinearOrder_1394 -> T_DecStrictPartialOrder_850
du_decStrictPartialOrder_1452 v0
  = coe
      du_decStrictPartialOrder_1348
      (coe du_strictTotalOrder_1424 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder._.irrefl
d_irrefl_1454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_1454 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.isDecEquivalence
d_isDecEquivalence_1456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_1456 ~v0 ~v1 ~v2 v3
  = du_isDecEquivalence_1456 v3
du_isDecEquivalence_1456 ::
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_1456 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_678
         (coe d_isStrictTotalOrder_1302 (coe v1)))
-- Relation.Binary.Bundles.DenseLinearOrder._.isDecStrictPartialOrder
d_isDecStrictPartialOrder_1458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
d_isDecStrictPartialOrder_1458 ~v0 ~v1 ~v2 v3
  = du_isDecStrictPartialOrder_1458 v3
du_isDecStrictPartialOrder_1458 ::
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
du_isDecStrictPartialOrder_1458 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecStrictPartialOrder_656
         (coe d_isStrictTotalOrder_1302 (coe v1)))
-- Relation.Binary.Bundles.DenseLinearOrder._.isEquivalence
d_isEquivalence_1460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1460 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1460 v3
du_isEquivalence_1460 ::
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1460 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe d_isStrictTotalOrder_1302 (coe v1))))
-- Relation.Binary.Bundles.DenseLinearOrder._.isStrictPartialOrder
d_isStrictPartialOrder_1462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_isStrictPartialOrder_1462 ~v0 ~v1 ~v2 v3
  = du_isStrictPartialOrder_1462 v3
du_isStrictPartialOrder_1462 ::
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_isStrictPartialOrder_1462 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictTotalOrder_694
         (coe d_isDenseLinearOrder_1416 (coe v0)))
-- Relation.Binary.Bundles.DenseLinearOrder._.rawRelation
d_rawRelation_1464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_1464 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.rawSetoid
d_rawSetoid_1466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1466 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.strictPartialOrder
d_strictPartialOrder_1468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> T_StrictPartialOrder_760
d_strictPartialOrder_1468 ~v0 ~v1 ~v2 v3
  = du_strictPartialOrder_1468 v3
du_strictPartialOrder_1468 ::
  T_DenseLinearOrder_1394 -> T_StrictPartialOrder_760
du_strictPartialOrder_1468 v0
  = coe
      du_strictPartialOrder_1318 (coe du_strictTotalOrder_1424 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder._.trans
d_trans_1470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1470 ~v0 ~v1 ~v2 v3 = du_trans_1470 v3
du_trans_1470 ::
  T_DenseLinearOrder_1394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1470 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_386
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe d_isStrictTotalOrder_1302 (coe v1))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq._≈_
d__'8776'__1474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1474 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq._≉_
d__'8777'__1476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1476 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq._≟_
d__'8799'__1478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__1478 ~v0 ~v1 ~v2 v3 = du__'8799'__1478 v3
du__'8799'__1478 ::
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__1478 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1348 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__430
            (coe d_isDecStrictPartialOrder_872 (coe v2))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.Carrier
d_Carrier_1480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> ()
d_Carrier_1480 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.decSetoid
d_decSetoid_1482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> T_DecSetoid_90
d_decSetoid_1482 ~v0 ~v1 ~v2 v3 = du_decSetoid_1482 v3
du_decSetoid_1482 :: T_DenseLinearOrder_1394 -> T_DecSetoid_90
du_decSetoid_1482 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (coe du_decSetoid_946 (coe du_decStrictPartialOrder_1348 (coe v1)))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.isDecEquivalence
d_isDecEquivalence_1484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_1484 ~v0 ~v1 ~v2 v3
  = du_isDecEquivalence_1484 v3
du_isDecEquivalence_1484 ::
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_1484 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1348 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_464
            (coe d_isDecStrictPartialOrder_872 (coe v2))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.isEquivalence
d_isEquivalence_1486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1486 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1486 v3
du_isEquivalence_1486 ::
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1486 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1348 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_428
               (coe d_isDecStrictPartialOrder_872 (coe v2)))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_1488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1488 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1488 v3
du_isPartialEquivalence_1488 ::
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1488 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1348 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_946 (coe v2) in
          coe
            (let v4 = coe du_setoid_114 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe d_isEquivalence_62 (coe v4))))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.partialSetoid
d_partialSetoid_1490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> T_PartialSetoid_10
d_partialSetoid_1490 ~v0 ~v1 ~v2 v3 = du_partialSetoid_1490 v3
du_partialSetoid_1490 ::
  T_DenseLinearOrder_1394 -> T_PartialSetoid_10
du_partialSetoid_1490 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1348 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_946 (coe v2) in
          coe (coe du_partialSetoid_72 (coe du_setoid_114 (coe v3)))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.rawSetoid
d_rawSetoid_1492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1492 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.refl
d_refl_1494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny
d_refl_1494 ~v0 ~v1 ~v2 v3 = du_refl_1494 v3
du_refl_1494 :: T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny
du_refl_1494 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1348 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_946 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_36
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
                  (coe d_isDecEquivalence_106 (coe v3))))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.reflexive
d_reflexive_1496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1496 ~v0 ~v1 ~v2 v3 = du_reflexive_1496 v3
du_reflexive_1496 ::
  T_DenseLinearOrder_1394 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1496 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1348 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_946 (coe v2) in
          coe
            (let v4 = coe du_setoid_114 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe d_isEquivalence_62 (coe v4)) v5))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.setoid
d_setoid_1498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> T_Setoid_46
d_setoid_1498 ~v0 ~v1 ~v2 v3 = du_setoid_1498 v3
du_setoid_1498 :: T_DenseLinearOrder_1394 -> T_Setoid_46
du_setoid_1498 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1348 (coe v1) in
       coe (coe du_setoid_114 (coe du_decSetoid_946 (coe v2))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.sym
d_sym_1500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1500 ~v0 ~v1 ~v2 v3 = du_sym_1500 v3
du_sym_1500 ::
  T_DenseLinearOrder_1394 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1500 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1348 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_946 (coe v2) in
          coe
            (let v4 = coe du_setoid_114 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe d_isEquivalence_62 (coe v4))))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.trans
d_trans_1502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1502 ~v0 ~v1 ~v2 v3 = du_trans_1502 v3
du_trans_1502 ::
  T_DenseLinearOrder_1394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1502 v0
  = let v1 = coe du_strictTotalOrder_1424 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1348 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_946 (coe v2) in
          coe
            (let v4 = coe du_setoid_114 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe d_isEquivalence_62 (coe v4))))))
-- Relation.Binary.Bundles.ApartnessRelation
d_ApartnessRelation_1512 a0 a1 a2 = ()
newtype T_ApartnessRelation_1512
  = C_constructor_1558 MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_750
-- Relation.Binary.Bundles.ApartnessRelation.Carrier
d_Carrier_1528 :: T_ApartnessRelation_1512 -> ()
d_Carrier_1528 = erased
-- Relation.Binary.Bundles.ApartnessRelation._≈_
d__'8776'__1530 ::
  T_ApartnessRelation_1512 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1530 = erased
-- Relation.Binary.Bundles.ApartnessRelation._#_
d__'35'__1532 ::
  T_ApartnessRelation_1512 -> AgdaAny -> AgdaAny -> ()
d__'35'__1532 = erased
-- Relation.Binary.Bundles.ApartnessRelation.isApartnessRelation
d_isApartnessRelation_1534 ::
  T_ApartnessRelation_1512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_750
d_isApartnessRelation_1534 v0
  = case coe v0 of
      C_constructor_1558 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.ApartnessRelation._.cotrans
d_cotrans_1538 ::
  T_ApartnessRelation_1512 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cotrans_1538 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_cotrans_764
      (coe d_isApartnessRelation_1534 (coe v0))
-- Relation.Binary.Bundles.ApartnessRelation._.irrefl
d_irrefl_1540 ::
  T_ApartnessRelation_1512 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_1540 = erased
-- Relation.Binary.Bundles.ApartnessRelation._.sym
d_sym_1542 ::
  T_ApartnessRelation_1512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1542 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_762
      (coe d_isApartnessRelation_1534 (coe v0))
-- Relation.Binary.Bundles.ApartnessRelation.rawRelation
d_rawRelation_1544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ApartnessRelation_1512 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawRelation_40
d_rawRelation_1544 = erased
-- Relation.Binary.Bundles.ApartnessRelation._._∼ᵒ_
d__'8764''7506'__1548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ApartnessRelation_1512 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__1548 = erased
-- Relation.Binary.Bundles.ApartnessRelation._._≁_
d__'8769'__1550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ApartnessRelation_1512 -> AgdaAny -> AgdaAny -> ()
d__'8769'__1550 = erased
-- Relation.Binary.Bundles.ApartnessRelation._._≁ᵒ_
d__'8769''7506'__1552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ApartnessRelation_1512 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__1552 = erased
-- Relation.Binary.Bundles.ApartnessRelation._._≉_
d__'8777'__1554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ApartnessRelation_1512 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1554 = erased
-- Relation.Binary.Bundles.ApartnessRelation._.rawSetoid
d_rawSetoid_1556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ApartnessRelation_1512 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1556 = erased
