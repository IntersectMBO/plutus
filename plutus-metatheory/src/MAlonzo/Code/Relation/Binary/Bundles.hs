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

module MAlonzo.Code.Relation.Binary.Bundles where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Bundles.PartialSetoid
d_PartialSetoid_10 a0 a1 = ()
newtype T_PartialSetoid_10
  = C_PartialSetoid'46'constructor_133 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
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
      C_PartialSetoid'46'constructor_133 v3 -> coe v3
      _                                     -> MAlonzo.RTE.mazUnreachableError
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
-- Relation.Binary.Bundles.PartialSetoid._≉_
d__'8777'__34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PartialSetoid_10 -> AgdaAny -> AgdaAny -> ()
d__'8777'__34 = erased
-- Relation.Binary.Bundles.Setoid
d_Setoid_44 a0 a1 = ()
newtype T_Setoid_44
  = C_Setoid'46'constructor_733 MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
-- Relation.Binary.Bundles.Setoid.Carrier
d_Carrier_56 :: T_Setoid_44 -> ()
d_Carrier_56 = erased
-- Relation.Binary.Bundles.Setoid._≈_
d__'8776'__58 :: T_Setoid_44 -> AgdaAny -> AgdaAny -> ()
d__'8776'__58 = erased
-- Relation.Binary.Bundles.Setoid.isEquivalence
d_isEquivalence_60 ::
  T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_60 v0
  = case coe v0 of
      C_Setoid'46'constructor_733 v3 -> coe v3
      _                              -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.Setoid._.isPartialEquivalence
d_isPartialEquivalence_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_64 ~v0 ~v1 v2
  = du_isPartialEquivalence_64 v2
du_isPartialEquivalence_64 ::
  T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_64 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
      (coe d_isEquivalence_60 (coe v0))
-- Relation.Binary.Bundles.Setoid._.refl
d_refl_66 :: T_Setoid_44 -> AgdaAny -> AgdaAny
d_refl_66 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence_60 (coe v0))
-- Relation.Binary.Bundles.Setoid._.reflexive
d_reflexive_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_68 ~v0 ~v1 v2 = du_reflexive_68 v2
du_reflexive_68 ::
  T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_68 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
      (coe d_isEquivalence_60 (coe v0)) v1
-- Relation.Binary.Bundles.Setoid.partialSetoid
d_partialSetoid_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_44 -> T_PartialSetoid_10
d_partialSetoid_70 ~v0 ~v1 v2 = du_partialSetoid_70 v2
du_partialSetoid_70 :: T_Setoid_44 -> T_PartialSetoid_10
du_partialSetoid_70 v0
  = coe
      C_PartialSetoid'46'constructor_133
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_60 (coe v0)))
-- Relation.Binary.Bundles.Setoid._._≉_
d__'8777'__74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_44 -> AgdaAny -> AgdaAny -> ()
d__'8777'__74 = erased
-- Relation.Binary.Bundles.Setoid._.sym
d_sym_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_44 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_76 ~v0 ~v1 v2 = du_sym_76 v2
du_sym_76 ::
  T_Setoid_44 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_76 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_isEquivalence_60 (coe v0))
-- Relation.Binary.Bundles.Setoid._.trans
d_trans_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Setoid_44 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_78 ~v0 ~v1 v2 = du_trans_78 v2
du_trans_78 ::
  T_Setoid_44 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_78 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_isEquivalence_60 (coe v0))
-- Relation.Binary.Bundles.DecSetoid
d_DecSetoid_84 a0 a1 = ()
newtype T_DecSetoid_84
  = C_DecSetoid'46'constructor_1389 MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
-- Relation.Binary.Bundles.DecSetoid.Carrier
d_Carrier_96 :: T_DecSetoid_84 -> ()
d_Carrier_96 = erased
-- Relation.Binary.Bundles.DecSetoid._≈_
d__'8776'__98 :: T_DecSetoid_84 -> AgdaAny -> AgdaAny -> ()
d__'8776'__98 = erased
-- Relation.Binary.Bundles.DecSetoid.isDecEquivalence
d_isDecEquivalence_100 ::
  T_DecSetoid_84 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_100 v0
  = case coe v0 of
      C_DecSetoid'46'constructor_1389 v3 -> coe v3
      _                                  -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.DecSetoid._._≟_
d__'8799'__104 ::
  T_DecSetoid_84 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__104 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52
      (coe d_isDecEquivalence_100 (coe v0))
-- Relation.Binary.Bundles.DecSetoid._.isEquivalence
d_isEquivalence_106 ::
  T_DecSetoid_84 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_106 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
      (coe d_isDecEquivalence_100 (coe v0))
-- Relation.Binary.Bundles.DecSetoid.setoid
d_setoid_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_84 -> T_Setoid_44
d_setoid_108 ~v0 ~v1 v2 = du_setoid_108 v2
du_setoid_108 :: T_DecSetoid_84 -> T_Setoid_44
du_setoid_108 v0
  = coe
      C_Setoid'46'constructor_733
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
         (coe d_isDecEquivalence_100 (coe v0)))
-- Relation.Binary.Bundles.DecSetoid._._≉_
d__'8777'__112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_84 -> AgdaAny -> AgdaAny -> ()
d__'8777'__112 = erased
-- Relation.Binary.Bundles.DecSetoid._.isPartialEquivalence
d_isPartialEquivalence_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_84 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_114 ~v0 ~v1 v2
  = du_isPartialEquivalence_114 v2
du_isPartialEquivalence_114 ::
  T_DecSetoid_84 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_114 v0
  = let v1 = coe du_setoid_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_60 (coe v1)))
-- Relation.Binary.Bundles.DecSetoid._.partialSetoid
d_partialSetoid_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_84 -> T_PartialSetoid_10
d_partialSetoid_116 ~v0 ~v1 v2 = du_partialSetoid_116 v2
du_partialSetoid_116 :: T_DecSetoid_84 -> T_PartialSetoid_10
du_partialSetoid_116 v0
  = coe du_partialSetoid_70 (coe du_setoid_108 (coe v0))
-- Relation.Binary.Bundles.DecSetoid._.refl
d_refl_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_84 -> AgdaAny -> AgdaAny
d_refl_118 ~v0 ~v1 v2 = du_refl_118 v2
du_refl_118 :: T_DecSetoid_84 -> AgdaAny -> AgdaAny
du_refl_118 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
         (coe d_isDecEquivalence_100 (coe v0)))
-- Relation.Binary.Bundles.DecSetoid._.reflexive
d_reflexive_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_84 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_120 ~v0 ~v1 v2 = du_reflexive_120 v2
du_reflexive_120 ::
  T_DecSetoid_84 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_120 v0
  = let v1 = coe du_setoid_108 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_60 (coe v1)) v2)
-- Relation.Binary.Bundles.DecSetoid._.sym
d_sym_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_84 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_122 ~v0 ~v1 v2 = du_sym_122 v2
du_sym_122 ::
  T_DecSetoid_84 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_122 v0
  = let v1 = coe du_setoid_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe d_isEquivalence_60 (coe v1)))
-- Relation.Binary.Bundles.DecSetoid._.trans
d_trans_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecSetoid_84 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_124 ~v0 ~v1 v2 = du_trans_124 v2
du_trans_124 ::
  T_DecSetoid_84 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_124 v0
  = let v1 = coe du_setoid_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe d_isEquivalence_60 (coe v1)))
-- Relation.Binary.Bundles.Preorder
d_Preorder_132 a0 a1 a2 = ()
newtype T_Preorder_132
  = C_Preorder'46'constructor_2267 MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
-- Relation.Binary.Bundles.Preorder.Carrier
d_Carrier_148 :: T_Preorder_132 -> ()
d_Carrier_148 = erased
-- Relation.Binary.Bundles.Preorder._≈_
d__'8776'__150 :: T_Preorder_132 -> AgdaAny -> AgdaAny -> ()
d__'8776'__150 = erased
-- Relation.Binary.Bundles.Preorder._≲_
d__'8818'__152 :: T_Preorder_132 -> AgdaAny -> AgdaAny -> ()
d__'8818'__152 = erased
-- Relation.Binary.Bundles.Preorder.isPreorder
d_isPreorder_154 ::
  T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_154 v0
  = case coe v0 of
      C_Preorder'46'constructor_2267 v4 -> coe v4
      _                                 -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.Preorder._.isEquivalence
d_isEquivalence_158 ::
  T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_158 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe d_isPreorder_154 (coe v0))
-- Relation.Binary.Bundles.Preorder._.refl
d_refl_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> AgdaAny -> AgdaAny
d_refl_160 ~v0 ~v1 ~v2 v3 = du_refl_160 v3
du_refl_160 :: T_Preorder_132 -> AgdaAny -> AgdaAny
du_refl_160 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_refl_98
      (coe d_isPreorder_154 (coe v0))
-- Relation.Binary.Bundles.Preorder._.reflexive
d_reflexive_162 ::
  T_Preorder_132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_162 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe d_isPreorder_154 (coe v0))
-- Relation.Binary.Bundles.Preorder._.trans
d_trans_164 ::
  T_Preorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_164 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe d_isPreorder_154 (coe v0))
-- Relation.Binary.Bundles.Preorder._.∼-resp-≈
d_'8764''45'resp'45''8776'_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_166 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_166 v3
du_'8764''45'resp'45''8776'_166 ::
  T_Preorder_132 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_166 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
      (coe d_isPreorder_154 (coe v0))
-- Relation.Binary.Bundles.Preorder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_168 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_168 v3
du_'8764''45'resp'691''45''8776'_168 ::
  T_Preorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_168 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
      (coe d_isPreorder_154 (coe v0))
-- Relation.Binary.Bundles.Preorder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_170 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_170 v3
du_'8764''45'resp'737''45''8776'_170 ::
  T_Preorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_170 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
      (coe d_isPreorder_154 (coe v0))
-- Relation.Binary.Bundles.Preorder._.≲-resp-≈
d_'8818''45'resp'45''8776'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_172 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_172 v3
du_'8818''45'resp'45''8776'_172 ::
  T_Preorder_132 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_172 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
      (coe d_isPreorder_154 (coe v0))
-- Relation.Binary.Bundles.Preorder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_174 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_174 v3
du_'8818''45'resp'691''45''8776'_174 ::
  T_Preorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_174 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
      (coe d_isPreorder_154 (coe v0))
-- Relation.Binary.Bundles.Preorder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_176 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_176 v3
du_'8818''45'resp'737''45''8776'_176 ::
  T_Preorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
      (coe d_isPreorder_154 (coe v0))
-- Relation.Binary.Bundles.Preorder.Eq.setoid
d_setoid_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> T_Setoid_44
d_setoid_180 ~v0 ~v1 ~v2 v3 = du_setoid_180 v3
du_setoid_180 :: T_Preorder_132 -> T_Setoid_44
du_setoid_180 v0
  = coe
      C_Setoid'46'constructor_733
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe d_isPreorder_154 (coe v0)))
-- Relation.Binary.Bundles.Preorder.Eq._._≈_
d__'8776'__184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> AgdaAny -> AgdaAny -> ()
d__'8776'__184 = erased
-- Relation.Binary.Bundles.Preorder.Eq._._≉_
d__'8777'__186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> AgdaAny -> AgdaAny -> ()
d__'8777'__186 = erased
-- Relation.Binary.Bundles.Preorder.Eq._.Carrier
d_Carrier_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_Preorder_132 -> ()
d_Carrier_188 = erased
-- Relation.Binary.Bundles.Preorder.Eq._.isEquivalence
d_isEquivalence_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_190 ~v0 ~v1 ~v2 v3 = du_isEquivalence_190 v3
du_isEquivalence_190 ::
  T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_190 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe d_isPreorder_154 (coe v0))
-- Relation.Binary.Bundles.Preorder.Eq._.isPartialEquivalence
d_isPartialEquivalence_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_192 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_192 v3
du_isPartialEquivalence_192 ::
  T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_192 v0
  = let v1 = coe du_setoid_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_60 (coe v1)))
-- Relation.Binary.Bundles.Preorder.Eq._.partialSetoid
d_partialSetoid_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> T_PartialSetoid_10
d_partialSetoid_194 ~v0 ~v1 ~v2 v3 = du_partialSetoid_194 v3
du_partialSetoid_194 :: T_Preorder_132 -> T_PartialSetoid_10
du_partialSetoid_194 v0
  = coe du_partialSetoid_70 (coe du_setoid_180 (coe v0))
-- Relation.Binary.Bundles.Preorder.Eq._.refl
d_refl_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> AgdaAny -> AgdaAny
d_refl_196 ~v0 ~v1 ~v2 v3 = du_refl_196 v3
du_refl_196 :: T_Preorder_132 -> AgdaAny -> AgdaAny
du_refl_196 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe d_isPreorder_154 (coe v0)))
-- Relation.Binary.Bundles.Preorder.Eq._.reflexive
d_reflexive_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_198 ~v0 ~v1 ~v2 v3 = du_reflexive_198 v3
du_reflexive_198 ::
  T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_198 v0
  = let v1 = coe du_setoid_180 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_60 (coe v1)) v2)
-- Relation.Binary.Bundles.Preorder.Eq._.sym
d_sym_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_200 ~v0 ~v1 ~v2 v3 = du_sym_200 v3
du_sym_200 ::
  T_Preorder_132 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_200 v0
  = let v1 = coe du_setoid_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe d_isEquivalence_60 (coe v1)))
-- Relation.Binary.Bundles.Preorder.Eq._.trans
d_trans_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_202 ~v0 ~v1 ~v2 v3 = du_trans_202 v3
du_trans_202 ::
  T_Preorder_132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_202 v0
  = let v1 = coe du_setoid_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe d_isEquivalence_60 (coe v1)))
-- Relation.Binary.Bundles.Preorder._⋦_
d__'8934'__204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> AgdaAny -> AgdaAny -> ()
d__'8934'__204 = erased
-- Relation.Binary.Bundles.Preorder._≳_
d__'8819'__210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> AgdaAny -> AgdaAny -> ()
d__'8819'__210 = erased
-- Relation.Binary.Bundles.Preorder._⋧_
d__'8935'__212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> AgdaAny -> AgdaAny -> ()
d__'8935'__212 = erased
-- Relation.Binary.Bundles.Preorder._∼_
d__'8764'__214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Preorder_132 -> AgdaAny -> AgdaAny -> ()
d__'8764'__214 = erased
-- Relation.Binary.Bundles.TotalPreorder
d_TotalPreorder_222 a0 a1 a2 = ()
newtype T_TotalPreorder_222
  = C_TotalPreorder'46'constructor_4573 MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
-- Relation.Binary.Bundles.TotalPreorder.Carrier
d_Carrier_238 :: T_TotalPreorder_222 -> ()
d_Carrier_238 = erased
-- Relation.Binary.Bundles.TotalPreorder._≈_
d__'8776'__240 :: T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> ()
d__'8776'__240 = erased
-- Relation.Binary.Bundles.TotalPreorder._≲_
d__'8818'__242 :: T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> ()
d__'8818'__242 = erased
-- Relation.Binary.Bundles.TotalPreorder.isTotalPreorder
d_isTotalPreorder_244 ::
  T_TotalPreorder_222 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
d_isTotalPreorder_244 v0
  = case coe v0 of
      C_TotalPreorder'46'constructor_4573 v4 -> coe v4
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.TotalPreorder._.isPreorder
d_isPreorder_248 ::
  T_TotalPreorder_222 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_248 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
      (coe d_isTotalPreorder_244 (coe v0))
-- Relation.Binary.Bundles.TotalPreorder._.total
d_total_250 ::
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_250 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_total_134
      (coe d_isTotalPreorder_244 (coe v0))
-- Relation.Binary.Bundles.TotalPreorder.preorder
d_preorder_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> T_Preorder_132
d_preorder_252 ~v0 ~v1 ~v2 v3 = du_preorder_252 v3
du_preorder_252 :: T_TotalPreorder_222 -> T_Preorder_132
du_preorder_252 v0
  = coe
      C_Preorder'46'constructor_2267
      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
         (coe d_isTotalPreorder_244 (coe v0)))
-- Relation.Binary.Bundles.TotalPreorder._._∼_
d__'8764'__256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> ()
d__'8764'__256 = erased
-- Relation.Binary.Bundles.TotalPreorder._._≳_
d__'8819'__258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> ()
d__'8819'__258 = erased
-- Relation.Binary.Bundles.TotalPreorder._._⋦_
d__'8934'__260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> ()
d__'8934'__260 = erased
-- Relation.Binary.Bundles.TotalPreorder._._⋧_
d__'8935'__262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> ()
d__'8935'__262 = erased
-- Relation.Binary.Bundles.TotalPreorder._.isEquivalence
d_isEquivalence_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_264 ~v0 ~v1 ~v2 v3 = du_isEquivalence_264 v3
du_isEquivalence_264 ::
  T_TotalPreorder_222 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_264 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
         (coe d_isTotalPreorder_244 (coe v0)))
-- Relation.Binary.Bundles.TotalPreorder._.refl
d_refl_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny
d_refl_266 ~v0 ~v1 ~v2 v3 = du_refl_266 v3
du_refl_266 :: T_TotalPreorder_222 -> AgdaAny -> AgdaAny
du_refl_266 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_98
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.reflexive
d_reflexive_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_268 ~v0 ~v1 ~v2 v3 = du_reflexive_268 v3
du_reflexive_268 ::
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_268 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
         (coe d_isTotalPreorder_244 (coe v0)))
-- Relation.Binary.Bundles.TotalPreorder._.trans
d_trans_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_270 ~v0 ~v1 ~v2 v3 = du_trans_270 v3
du_trans_270 ::
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_270 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132
         (coe d_isTotalPreorder_244 (coe v0)))
-- Relation.Binary.Bundles.TotalPreorder._.∼-resp-≈
d_'8764''45'resp'45''8776'_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_272 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_272 v3
du_'8764''45'resp'45''8776'_272 ::
  T_TotalPreorder_222 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_272 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_274 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_274 v3
du_'8764''45'resp'691''45''8776'_274 ::
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_274 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_276 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_276 v3
du_'8764''45'resp'737''45''8776'_276 ::
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_276 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.≲-resp-≈
d_'8818''45'resp'45''8776'_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_278 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_278 v3
du_'8818''45'resp'45''8776'_278 ::
  T_TotalPreorder_222 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_278 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_280 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_280 v3
du_'8818''45'resp'691''45''8776'_280 ::
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_280 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_282 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_282 v3
du_'8818''45'resp'737''45''8776'_282 ::
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_282 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.Eq._≈_
d__'8776'__286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> ()
d__'8776'__286 = erased
-- Relation.Binary.Bundles.TotalPreorder._.Eq._≉_
d__'8777'__288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> ()
d__'8777'__288 = erased
-- Relation.Binary.Bundles.TotalPreorder._.Eq.Carrier
d_Carrier_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_TotalPreorder_222 -> ()
d_Carrier_290 = erased
-- Relation.Binary.Bundles.TotalPreorder._.Eq.isEquivalence
d_isEquivalence_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_292 ~v0 ~v1 ~v2 v3 = du_isEquivalence_292 v3
du_isEquivalence_292 ::
  T_TotalPreorder_222 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_292 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.isPartialEquivalence
d_isPartialEquivalence_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_294 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_294 v3
du_isPartialEquivalence_294 ::
  T_TotalPreorder_222 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_294 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (let v2 = coe du_setoid_180 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.partialSetoid
d_partialSetoid_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> T_PartialSetoid_10
d_partialSetoid_296 ~v0 ~v1 ~v2 v3 = du_partialSetoid_296 v3
du_partialSetoid_296 :: T_TotalPreorder_222 -> T_PartialSetoid_10
du_partialSetoid_296 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe (coe du_partialSetoid_70 (coe du_setoid_180 (coe v1)))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.refl
d_refl_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny
d_refl_298 ~v0 ~v1 ~v2 v3 = du_refl_298 v3
du_refl_298 :: T_TotalPreorder_222 -> AgdaAny -> AgdaAny
du_refl_298 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe d_isPreorder_154 (coe v1))))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.reflexive
d_reflexive_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_300 ~v0 ~v1 ~v2 v3 = du_reflexive_300 v3
du_reflexive_300 ::
  T_TotalPreorder_222 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_300 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (let v2 = coe du_setoid_180 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe d_isEquivalence_60 (coe v2)) v3))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.setoid
d_setoid_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> T_Setoid_44
d_setoid_302 ~v0 ~v1 ~v2 v3 = du_setoid_302 v3
du_setoid_302 :: T_TotalPreorder_222 -> T_Setoid_44
du_setoid_302 v0 = coe du_setoid_180 (coe du_preorder_252 (coe v0))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.sym
d_sym_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_304 ~v0 ~v1 ~v2 v3 = du_sym_304 v3
du_sym_304 ::
  T_TotalPreorder_222 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_304 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (let v2 = coe du_setoid_180 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.TotalPreorder._.Eq.trans
d_trans_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_306 ~v0 ~v1 ~v2 v3 = du_trans_306 v3
du_trans_306 ::
  T_TotalPreorder_222 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_306 v0
  = let v1 = coe du_preorder_252 (coe v0) in
    coe
      (let v2 = coe du_setoid_180 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.Poset
d_Poset_314 a0 a1 a2 = ()
newtype T_Poset_314
  = C_Poset'46'constructor_6389 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
-- Relation.Binary.Bundles.Poset.Carrier
d_Carrier_330 :: T_Poset_314 -> ()
d_Carrier_330 = erased
-- Relation.Binary.Bundles.Poset._≈_
d__'8776'__332 :: T_Poset_314 -> AgdaAny -> AgdaAny -> ()
d__'8776'__332 = erased
-- Relation.Binary.Bundles.Poset._≤_
d__'8804'__334 :: T_Poset_314 -> AgdaAny -> AgdaAny -> ()
d__'8804'__334 = erased
-- Relation.Binary.Bundles.Poset.isPartialOrder
d_isPartialOrder_336 ::
  T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_336 v0
  = case coe v0 of
      C_Poset'46'constructor_6389 v4 -> coe v4
      _                              -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.Poset._.antisym
d_antisym_340 ::
  T_Poset_314 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_340 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe d_isPartialOrder_336 (coe v0))
-- Relation.Binary.Bundles.Poset._.isPreorder
d_isPreorder_342 ::
  T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_342 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe d_isPartialOrder_336 (coe v0))
-- Relation.Binary.Bundles.Poset.preorder
d_preorder_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> T_Preorder_132
d_preorder_344 ~v0 ~v1 ~v2 v3 = du_preorder_344 v3
du_preorder_344 :: T_Poset_314 -> T_Preorder_132
du_preorder_344 v0
  = coe
      C_Preorder'46'constructor_2267
      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_336 (coe v0)))
-- Relation.Binary.Bundles.Poset._._∼_
d__'8764'__348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> AgdaAny -> AgdaAny -> ()
d__'8764'__348 = erased
-- Relation.Binary.Bundles.Poset._._≳_
d__'8819'__350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> AgdaAny -> AgdaAny -> ()
d__'8819'__350 = erased
-- Relation.Binary.Bundles.Poset._._⋦_
d__'8934'__352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> AgdaAny -> AgdaAny -> ()
d__'8934'__352 = erased
-- Relation.Binary.Bundles.Poset._._⋧_
d__'8935'__354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> AgdaAny -> AgdaAny -> ()
d__'8935'__354 = erased
-- Relation.Binary.Bundles.Poset._.isEquivalence
d_isEquivalence_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_356 ~v0 ~v1 ~v2 v3 = du_isEquivalence_356 v3
du_isEquivalence_356 ::
  T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_356 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_336 (coe v0)))
-- Relation.Binary.Bundles.Poset._.refl
d_refl_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> AgdaAny -> AgdaAny
d_refl_358 ~v0 ~v1 ~v2 v3 = du_refl_358 v3
du_refl_358 :: T_Poset_314 -> AgdaAny -> AgdaAny
du_refl_358 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_98
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.Poset._.reflexive
d_reflexive_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_360 ~v0 ~v1 ~v2 v3 = du_reflexive_360 v3
du_reflexive_360 ::
  T_Poset_314 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_360 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_336 (coe v0)))
-- Relation.Binary.Bundles.Poset._.trans
d_trans_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_362 ~v0 ~v1 ~v2 v3 = du_trans_362 v3
du_trans_362 ::
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_362 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_336 (coe v0)))
-- Relation.Binary.Bundles.Poset._.∼-resp-≈
d_'8764''45'resp'45''8776'_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_364 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_364 v3
du_'8764''45'resp'45''8776'_364 ::
  T_Poset_314 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_364 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.Poset._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_366 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_366 v3
du_'8764''45'resp'691''45''8776'_366 ::
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_366 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.Poset._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_368 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_368 v3
du_'8764''45'resp'737''45''8776'_368 ::
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_368 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.Poset._.≲-resp-≈
d_'8818''45'resp'45''8776'_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_370 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_370 v3
du_'8818''45'resp'45''8776'_370 ::
  T_Poset_314 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_370 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.Poset._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_372 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_372 v3
du_'8818''45'resp'691''45''8776'_372 ::
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_372 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.Poset._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_374 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_374 v3
du_'8818''45'resp'737''45''8776'_374 ::
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_374 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.Poset._.Eq._≈_
d__'8776'__378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> AgdaAny -> AgdaAny -> ()
d__'8776'__378 = erased
-- Relation.Binary.Bundles.Poset._.Eq._≉_
d__'8777'__380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> AgdaAny -> AgdaAny -> ()
d__'8777'__380 = erased
-- Relation.Binary.Bundles.Poset._.Eq.Carrier
d_Carrier_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_Poset_314 -> ()
d_Carrier_382 = erased
-- Relation.Binary.Bundles.Poset._.Eq.isEquivalence
d_isEquivalence_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_384 ~v0 ~v1 ~v2 v3 = du_isEquivalence_384 v3
du_isEquivalence_384 ::
  T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_384 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe d_isPreorder_154 (coe v1)))
-- Relation.Binary.Bundles.Poset._.Eq.isPartialEquivalence
d_isPartialEquivalence_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_386 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_386 v3
du_isPartialEquivalence_386 ::
  T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_386 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (let v2 = coe du_setoid_180 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.Poset._.Eq.partialSetoid
d_partialSetoid_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> T_PartialSetoid_10
d_partialSetoid_388 ~v0 ~v1 ~v2 v3 = du_partialSetoid_388 v3
du_partialSetoid_388 :: T_Poset_314 -> T_PartialSetoid_10
du_partialSetoid_388 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe (coe du_partialSetoid_70 (coe du_setoid_180 (coe v1)))
-- Relation.Binary.Bundles.Poset._.Eq.refl
d_refl_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> AgdaAny -> AgdaAny
d_refl_390 ~v0 ~v1 ~v2 v3 = du_refl_390 v3
du_refl_390 :: T_Poset_314 -> AgdaAny -> AgdaAny
du_refl_390 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe d_isPreorder_154 (coe v1))))
-- Relation.Binary.Bundles.Poset._.Eq.reflexive
d_reflexive_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_392 ~v0 ~v1 ~v2 v3 = du_reflexive_392 v3
du_reflexive_392 ::
  T_Poset_314 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_392 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (let v2 = coe du_setoid_180 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe d_isEquivalence_60 (coe v2)) v3))
-- Relation.Binary.Bundles.Poset._.Eq.setoid
d_setoid_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> T_Setoid_44
d_setoid_394 ~v0 ~v1 ~v2 v3 = du_setoid_394 v3
du_setoid_394 :: T_Poset_314 -> T_Setoid_44
du_setoid_394 v0 = coe du_setoid_180 (coe du_preorder_344 (coe v0))
-- Relation.Binary.Bundles.Poset._.Eq.sym
d_sym_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_396 ~v0 ~v1 ~v2 v3 = du_sym_396 v3
du_sym_396 ::
  T_Poset_314 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_396 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (let v2 = coe du_setoid_180 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.Poset._.Eq.trans
d_trans_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_398 ~v0 ~v1 ~v2 v3 = du_trans_398 v3
du_trans_398 ::
  T_Poset_314 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_398 v0
  = let v1 = coe du_preorder_344 (coe v0) in
    coe
      (let v2 = coe du_setoid_180 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.DecPoset
d_DecPoset_406 a0 a1 a2 = ()
newtype T_DecPoset_406
  = C_DecPoset'46'constructor_8213 MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
-- Relation.Binary.Bundles.DecPoset.Carrier
d_Carrier_422 :: T_DecPoset_406 -> ()
d_Carrier_422 = erased
-- Relation.Binary.Bundles.DecPoset._≈_
d__'8776'__424 :: T_DecPoset_406 -> AgdaAny -> AgdaAny -> ()
d__'8776'__424 = erased
-- Relation.Binary.Bundles.DecPoset._≤_
d__'8804'__426 :: T_DecPoset_406 -> AgdaAny -> AgdaAny -> ()
d__'8804'__426 = erased
-- Relation.Binary.Bundles.DecPoset.isDecPartialOrder
d_isDecPartialOrder_428 ::
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
d_isDecPartialOrder_428 v0
  = case coe v0 of
      C_DecPoset'46'constructor_8213 v4 -> coe v4
      _                                 -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.DecPoset.DPO._≟_
d__'8799'__432 ::
  T_DecPoset_406 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__432 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__236
      (coe d_isDecPartialOrder_428 (coe v0))
-- Relation.Binary.Bundles.DecPoset.DPO._≤?_
d__'8804''63'__434 ::
  T_DecPoset_406 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__434 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__238
      (coe d_isDecPartialOrder_428 (coe v0))
-- Relation.Binary.Bundles.DecPoset.DPO.isPartialOrder
d_isPartialOrder_440 ::
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_440 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_234
      (coe d_isDecPartialOrder_428 (coe v0))
-- Relation.Binary.Bundles.DecPoset.poset
d_poset_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> T_Poset_314
d_poset_480 ~v0 ~v1 ~v2 v3 = du_poset_480 v3
du_poset_480 :: T_DecPoset_406 -> T_Poset_314
du_poset_480 v0
  = coe
      C_Poset'46'constructor_6389
      (MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_234
         (coe d_isDecPartialOrder_428 (coe v0)))
-- Relation.Binary.Bundles.DecPoset._._∼_
d__'8764'__484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> AgdaAny -> AgdaAny -> ()
d__'8764'__484 = erased
-- Relation.Binary.Bundles.DecPoset._._≳_
d__'8819'__486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> AgdaAny -> AgdaAny -> ()
d__'8819'__486 = erased
-- Relation.Binary.Bundles.DecPoset._._⋦_
d__'8934'__488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> AgdaAny -> AgdaAny -> ()
d__'8934'__488 = erased
-- Relation.Binary.Bundles.DecPoset._._⋧_
d__'8935'__490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> AgdaAny -> AgdaAny -> ()
d__'8935'__490 = erased
-- Relation.Binary.Bundles.DecPoset._.antisym
d_antisym_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_492 ~v0 ~v1 ~v2 v3 = du_antisym_492 v3
du_antisym_492 ::
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_492 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_234
         (coe d_isDecPartialOrder_428 (coe v0)))
-- Relation.Binary.Bundles.DecPoset._.isEquivalence
d_isEquivalence_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_494 ~v0 ~v1 ~v2 v3 = du_isEquivalence_494 v3
du_isEquivalence_494 ::
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_494 v0
  = let v1 = coe du_poset_480 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_336 (coe v1))))
-- Relation.Binary.Bundles.DecPoset._.isPreorder
d_isPreorder_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_496 ~v0 ~v1 ~v2 v3 = du_isPreorder_496 v3
du_isPreorder_496 ::
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder_496 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_234
         (coe d_isDecPartialOrder_428 (coe v0)))
-- Relation.Binary.Bundles.DecPoset._.preorder
d_preorder_498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> T_Preorder_132
d_preorder_498 ~v0 ~v1 ~v2 v3 = du_preorder_498 v3
du_preorder_498 :: T_DecPoset_406 -> T_Preorder_132
du_preorder_498 v0
  = coe du_preorder_344 (coe du_poset_480 (coe v0))
-- Relation.Binary.Bundles.DecPoset._.refl
d_refl_500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> AgdaAny -> AgdaAny
d_refl_500 ~v0 ~v1 ~v2 v3 = du_refl_500 v3
du_refl_500 :: T_DecPoset_406 -> AgdaAny -> AgdaAny
du_refl_500 v0
  = let v1 = coe du_poset_480 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.reflexive
d_reflexive_502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_502 ~v0 ~v1 ~v2 v3 = du_reflexive_502 v3
du_reflexive_502 ::
  T_DecPoset_406 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_502 v0
  = let v1 = coe du_poset_480 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_336 (coe v1))))
-- Relation.Binary.Bundles.DecPoset._.trans
d_trans_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_504 ~v0 ~v1 ~v2 v3 = du_trans_504 v3
du_trans_504 ::
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_504 v0
  = let v1 = coe du_poset_480 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_84
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_336 (coe v1))))
-- Relation.Binary.Bundles.DecPoset._.∼-resp-≈
d_'8764''45'resp'45''8776'_506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_506 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_506 v3
du_'8764''45'resp'45''8776'_506 ::
  T_DecPoset_406 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_506 v0
  = let v1 = coe du_poset_480 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_508 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_508 v3
du_'8764''45'resp'691''45''8776'_508 ::
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_508 v0
  = let v1 = coe du_poset_480 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_510 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_510 v3
du_'8764''45'resp'737''45''8776'_510 ::
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_510 v0
  = let v1 = coe du_poset_480 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.≲-resp-≈
d_'8818''45'resp'45''8776'_512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_512 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_512 v3
du_'8818''45'resp'45''8776'_512 ::
  T_DecPoset_406 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_512 v0
  = let v1 = coe du_poset_480 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_514 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_514 v3
du_'8818''45'resp'691''45''8776'_514 ::
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_514 v0
  = let v1 = coe du_poset_480 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.DecPoset._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_516 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_516 v3
du_'8818''45'resp'737''45''8776'_516 ::
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_516 v0
  = let v1 = coe du_poset_480 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.DecPoset.Eq.decSetoid
d_decSetoid_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> T_DecSetoid_84
d_decSetoid_520 ~v0 ~v1 ~v2 v3 = du_decSetoid_520 v3
du_decSetoid_520 :: T_DecPoset_406 -> T_DecSetoid_84
du_decSetoid_520 v0
  = coe
      C_DecSetoid'46'constructor_1389
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_268
         (coe d_isDecPartialOrder_428 (coe v0)))
-- Relation.Binary.Bundles.DecPoset.Eq._._≈_
d__'8776'__524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> AgdaAny -> AgdaAny -> ()
d__'8776'__524 = erased
-- Relation.Binary.Bundles.DecPoset.Eq._._≉_
d__'8777'__526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> AgdaAny -> AgdaAny -> ()
d__'8777'__526 = erased
-- Relation.Binary.Bundles.DecPoset.Eq._._≟_
d__'8799'__528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__528 ~v0 ~v1 ~v2 v3 = du__'8799'__528 v3
du__'8799'__528 ::
  T_DecPoset_406 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__528 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__236
      (coe d_isDecPartialOrder_428 (coe v0))
-- Relation.Binary.Bundles.DecPoset.Eq._.Carrier
d_Carrier_530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_DecPoset_406 -> ()
d_Carrier_530 = erased
-- Relation.Binary.Bundles.DecPoset.Eq._.isDecEquivalence
d_isDecEquivalence_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_532 ~v0 ~v1 ~v2 v3 = du_isDecEquivalence_532 v3
du_isDecEquivalence_532 ::
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_isDecEquivalence_532 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_268
      (coe d_isDecPartialOrder_428 (coe v0))
-- Relation.Binary.Bundles.DecPoset.Eq._.isEquivalence
d_isEquivalence_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_534 ~v0 ~v1 ~v2 v3 = du_isEquivalence_534 v3
du_isEquivalence_534 ::
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_534 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_234
            (coe d_isDecPartialOrder_428 (coe v0))))
-- Relation.Binary.Bundles.DecPoset.Eq._.isPartialEquivalence
d_isPartialEquivalence_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_536 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_536 v3
du_isPartialEquivalence_536 ::
  T_DecPoset_406 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_536 v0
  = let v1 = coe du_decSetoid_520 (coe v0) in
    coe
      (let v2 = coe du_setoid_108 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.DecPoset.Eq._.partialSetoid
d_partialSetoid_538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> T_PartialSetoid_10
d_partialSetoid_538 ~v0 ~v1 ~v2 v3 = du_partialSetoid_538 v3
du_partialSetoid_538 :: T_DecPoset_406 -> T_PartialSetoid_10
du_partialSetoid_538 v0
  = let v1 = coe du_decSetoid_520 (coe v0) in
    coe (coe du_partialSetoid_70 (coe du_setoid_108 (coe v1)))
-- Relation.Binary.Bundles.DecPoset.Eq._.refl
d_refl_540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> AgdaAny -> AgdaAny
d_refl_540 ~v0 ~v1 ~v2 v3 = du_refl_540 v3
du_refl_540 :: T_DecPoset_406 -> AgdaAny -> AgdaAny
du_refl_540 v0
  = let v1 = coe du_decSetoid_520 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
            (coe d_isDecEquivalence_100 (coe v1))))
-- Relation.Binary.Bundles.DecPoset.Eq._.reflexive
d_reflexive_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_542 ~v0 ~v1 ~v2 v3 = du_reflexive_542 v3
du_reflexive_542 ::
  T_DecPoset_406 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_542 v0
  = let v1 = coe du_decSetoid_520 (coe v0) in
    coe
      (let v2 = coe du_setoid_108 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe d_isEquivalence_60 (coe v2)) v3))
-- Relation.Binary.Bundles.DecPoset.Eq._.setoid
d_setoid_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> T_Setoid_44
d_setoid_544 ~v0 ~v1 ~v2 v3 = du_setoid_544 v3
du_setoid_544 :: T_DecPoset_406 -> T_Setoid_44
du_setoid_544 v0
  = coe du_setoid_108 (coe du_decSetoid_520 (coe v0))
-- Relation.Binary.Bundles.DecPoset.Eq._.sym
d_sym_546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_546 ~v0 ~v1 ~v2 v3 = du_sym_546 v3
du_sym_546 ::
  T_DecPoset_406 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_546 v0
  = let v1 = coe du_decSetoid_520 (coe v0) in
    coe
      (let v2 = coe du_setoid_108 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.DecPoset.Eq._.trans
d_trans_548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_548 ~v0 ~v1 ~v2 v3 = du_trans_548 v3
du_trans_548 ::
  T_DecPoset_406 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_548 v0
  = let v1 = coe du_decSetoid_520 (coe v0) in
    coe
      (let v2 = coe du_setoid_108 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.StrictPartialOrder
d_StrictPartialOrder_556 a0 a1 a2 = ()
newtype T_StrictPartialOrder_556
  = C_StrictPartialOrder'46'constructor_11097 MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
-- Relation.Binary.Bundles.StrictPartialOrder.Carrier
d_Carrier_572 :: T_StrictPartialOrder_556 -> ()
d_Carrier_572 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._≈_
d__'8776'__574 ::
  T_StrictPartialOrder_556 -> AgdaAny -> AgdaAny -> ()
d__'8776'__574 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._<_
d__'60'__576 ::
  T_StrictPartialOrder_556 -> AgdaAny -> AgdaAny -> ()
d__'60'__576 = erased
-- Relation.Binary.Bundles.StrictPartialOrder.isStrictPartialOrder
d_isStrictPartialOrder_578 ::
  T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_isStrictPartialOrder_578 v0
  = case coe v0 of
      C_StrictPartialOrder'46'constructor_11097 v4 -> coe v4
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.StrictPartialOrder._.<-resp-≈
d_'60''45'resp'45''8776'_582 ::
  T_StrictPartialOrder_556 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_582 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
      (coe d_isStrictPartialOrder_578 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_584 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_584 v3
du_'60''45'resp'691''45''8776'_584 ::
  T_StrictPartialOrder_556 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_584 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_328
      (coe d_isStrictPartialOrder_578 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_586 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_586 v3
du_'60''45'resp'737''45''8776'_586 ::
  T_StrictPartialOrder_556 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_586 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_330
      (coe d_isStrictPartialOrder_578 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder._.asym
d_asym_588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_588 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._.irrefl
d_irrefl_590 ::
  T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_590 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._.isEquivalence
d_isEquivalence_592 ::
  T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_592 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
      (coe d_isStrictPartialOrder_578 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder._.trans
d_trans_594 ::
  T_StrictPartialOrder_556 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_594 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_306
      (coe d_isStrictPartialOrder_578 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq.setoid
d_setoid_598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 -> T_Setoid_44
d_setoid_598 ~v0 ~v1 ~v2 v3 = du_setoid_598 v3
du_setoid_598 :: T_StrictPartialOrder_556 -> T_Setoid_44
du_setoid_598 v0
  = coe
      C_Setoid'46'constructor_733
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
         (coe d_isStrictPartialOrder_578 (coe v0)))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._._≈_
d__'8776'__602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 -> AgdaAny -> AgdaAny -> ()
d__'8776'__602 = erased
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._._≉_
d__'8777'__604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 -> AgdaAny -> AgdaAny -> ()
d__'8777'__604 = erased
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.Carrier
d_Carrier_606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 -> ()
d_Carrier_606 = erased
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.isEquivalence
d_isEquivalence_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_608 ~v0 ~v1 ~v2 v3 = du_isEquivalence_608 v3
du_isEquivalence_608 ::
  T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_608 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
      (coe d_isStrictPartialOrder_578 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.isPartialEquivalence
d_isPartialEquivalence_610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_610 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_610 v3
du_isPartialEquivalence_610 ::
  T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_610 v0
  = let v1 = coe du_setoid_598 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_isEquivalence_60 (coe v1)))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.partialSetoid
d_partialSetoid_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 -> T_PartialSetoid_10
d_partialSetoid_612 ~v0 ~v1 ~v2 v3 = du_partialSetoid_612 v3
du_partialSetoid_612 ::
  T_StrictPartialOrder_556 -> T_PartialSetoid_10
du_partialSetoid_612 v0
  = coe du_partialSetoid_70 (coe du_setoid_598 (coe v0))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.refl
d_refl_614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 -> AgdaAny -> AgdaAny
d_refl_614 ~v0 ~v1 ~v2 v3 = du_refl_614 v3
du_refl_614 :: T_StrictPartialOrder_556 -> AgdaAny -> AgdaAny
du_refl_614 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
         (coe d_isStrictPartialOrder_578 (coe v0)))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.reflexive
d_reflexive_616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_616 ~v0 ~v1 ~v2 v3 = du_reflexive_616 v3
du_reflexive_616 ::
  T_StrictPartialOrder_556 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_616 v0
  = let v1 = coe du_setoid_598 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_isEquivalence_60 (coe v1)) v2)
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.sym
d_sym_618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_618 ~v0 ~v1 ~v2 v3 = du_sym_618 v3
du_sym_618 ::
  T_StrictPartialOrder_556 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_618 v0
  = let v1 = coe du_setoid_598 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe d_isEquivalence_60 (coe v1)))
-- Relation.Binary.Bundles.StrictPartialOrder.Eq._.trans
d_trans_620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_620 ~v0 ~v1 ~v2 v3 = du_trans_620 v3
du_trans_620 ::
  T_StrictPartialOrder_556 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_620 v0
  = let v1 = coe du_setoid_598 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe d_isEquivalence_60 (coe v1)))
-- Relation.Binary.Bundles.StrictPartialOrder._≮_
d__'8814'__622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 -> AgdaAny -> AgdaAny -> ()
d__'8814'__622 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._>_
d__'62'__628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 -> AgdaAny -> AgdaAny -> ()
d__'62'__628 = erased
-- Relation.Binary.Bundles.StrictPartialOrder._≯_
d__'8815'__630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictPartialOrder_556 -> AgdaAny -> AgdaAny -> ()
d__'8815'__630 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder
d_DecStrictPartialOrder_638 a0 a1 a2 = ()
newtype T_DecStrictPartialOrder_638
  = C_DecStrictPartialOrder'46'constructor_13245 MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
-- Relation.Binary.Bundles.DecStrictPartialOrder.Carrier
d_Carrier_654 :: T_DecStrictPartialOrder_638 -> ()
d_Carrier_654 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._≈_
d__'8776'__656 ::
  T_DecStrictPartialOrder_638 -> AgdaAny -> AgdaAny -> ()
d__'8776'__656 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._<_
d__'60'__658 ::
  T_DecStrictPartialOrder_638 -> AgdaAny -> AgdaAny -> ()
d__'60'__658 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder.isDecStrictPartialOrder
d_isDecStrictPartialOrder_660 ::
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
d_isDecStrictPartialOrder_660 v0
  = case coe v0 of
      C_DecStrictPartialOrder'46'constructor_13245 v4 -> coe v4
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.DecStrictPartialOrder.DSPO._<?_
d__'60''63'__664 ::
  T_DecStrictPartialOrder_638 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__664 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'60''63'__350
      (coe d_isDecStrictPartialOrder_660 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.DSPO._≟_
d__'8799'__666 ::
  T_DecStrictPartialOrder_638 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__666 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__348
      (coe d_isDecStrictPartialOrder_660 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.DSPO.isStrictPartialOrder
d_isStrictPartialOrder_680 ::
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_isStrictPartialOrder_680 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
      (coe d_isDecStrictPartialOrder_660 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.strictPartialOrder
d_strictPartialOrder_702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 -> T_StrictPartialOrder_556
d_strictPartialOrder_702 ~v0 ~v1 ~v2 v3
  = du_strictPartialOrder_702 v3
du_strictPartialOrder_702 ::
  T_DecStrictPartialOrder_638 -> T_StrictPartialOrder_556
du_strictPartialOrder_702 v0
  = coe
      C_StrictPartialOrder'46'constructor_11097
      (MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
         (coe d_isDecStrictPartialOrder_660 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder._._>_
d__'62'__706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 -> AgdaAny -> AgdaAny -> ()
d__'62'__706 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._._≮_
d__'8814'__708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 -> AgdaAny -> AgdaAny -> ()
d__'8814'__708 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._._≯_
d__'8815'__710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 -> AgdaAny -> AgdaAny -> ()
d__'8815'__710 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._.<-resp-≈
d_'60''45'resp'45''8776'_712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_712 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_712 v3
du_'60''45'resp'45''8776'_712 ::
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_712 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
         (coe d_isDecStrictPartialOrder_660 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_714 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_714 v3
du_'60''45'resp'691''45''8776'_714 ::
  T_DecStrictPartialOrder_638 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_714 v0
  = let v1 = coe du_strictPartialOrder_702 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_328
         (coe d_isStrictPartialOrder_578 (coe v1)))
-- Relation.Binary.Bundles.DecStrictPartialOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_716 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_716 v3
du_'60''45'resp'737''45''8776'_716 ::
  T_DecStrictPartialOrder_638 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_716 v0
  = let v1 = coe du_strictPartialOrder_702 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_330
         (coe d_isStrictPartialOrder_578 (coe v1)))
-- Relation.Binary.Bundles.DecStrictPartialOrder._.asym
d_asym_718 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_718 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._.irrefl
d_irrefl_720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_720 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder._.isEquivalence
d_isEquivalence_722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_722 ~v0 ~v1 ~v2 v3 = du_isEquivalence_722 v3
du_isEquivalence_722 ::
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_722 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
         (coe d_isDecStrictPartialOrder_660 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder._.trans
d_trans_724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_724 ~v0 ~v1 ~v2 v3 = du_trans_724 v3
du_trans_724 ::
  T_DecStrictPartialOrder_638 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_724 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_306
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
         (coe d_isDecStrictPartialOrder_660 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq.decSetoid
d_decSetoid_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 -> T_DecSetoid_84
d_decSetoid_728 ~v0 ~v1 ~v2 v3 = du_decSetoid_728 v3
du_decSetoid_728 :: T_DecStrictPartialOrder_638 -> T_DecSetoid_84
du_decSetoid_728 v0
  = coe
      C_DecSetoid'46'constructor_1389
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_382
         (coe d_isDecStrictPartialOrder_660 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._._≈_
d__'8776'__732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 -> AgdaAny -> AgdaAny -> ()
d__'8776'__732 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._._≉_
d__'8777'__734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 -> AgdaAny -> AgdaAny -> ()
d__'8777'__734 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._._≟_
d__'8799'__736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__736 ~v0 ~v1 ~v2 v3 = du__'8799'__736 v3
du__'8799'__736 ::
  T_DecStrictPartialOrder_638 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__736 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__348
      (coe d_isDecStrictPartialOrder_660 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.Carrier
d_Carrier_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 -> ()
d_Carrier_738 = erased
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.isDecEquivalence
d_isDecEquivalence_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_740 ~v0 ~v1 ~v2 v3 = du_isDecEquivalence_740 v3
du_isDecEquivalence_740 ::
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_isDecEquivalence_740 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_382
      (coe d_isDecStrictPartialOrder_660 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.isEquivalence
d_isEquivalence_742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_742 ~v0 ~v1 ~v2 v3 = du_isEquivalence_742 v3
du_isEquivalence_742 ::
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_742 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
         (coe d_isDecStrictPartialOrder_660 (coe v0)))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.isPartialEquivalence
d_isPartialEquivalence_744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_744 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_744 v3
du_isPartialEquivalence_744 ::
  T_DecStrictPartialOrder_638 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_744 v0
  = let v1 = coe du_decSetoid_728 (coe v0) in
    coe
      (let v2 = coe du_setoid_108 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.partialSetoid
d_partialSetoid_746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 -> T_PartialSetoid_10
d_partialSetoid_746 ~v0 ~v1 ~v2 v3 = du_partialSetoid_746 v3
du_partialSetoid_746 ::
  T_DecStrictPartialOrder_638 -> T_PartialSetoid_10
du_partialSetoid_746 v0
  = let v1 = coe du_decSetoid_728 (coe v0) in
    coe (coe du_partialSetoid_70 (coe du_setoid_108 (coe v1)))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.refl
d_refl_748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 -> AgdaAny -> AgdaAny
d_refl_748 ~v0 ~v1 ~v2 v3 = du_refl_748 v3
du_refl_748 :: T_DecStrictPartialOrder_638 -> AgdaAny -> AgdaAny
du_refl_748 v0
  = let v1 = coe du_decSetoid_728 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
            (coe d_isDecEquivalence_100 (coe v1))))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.reflexive
d_reflexive_750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_750 ~v0 ~v1 ~v2 v3 = du_reflexive_750 v3
du_reflexive_750 ::
  T_DecStrictPartialOrder_638 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_750 v0
  = let v1 = coe du_decSetoid_728 (coe v0) in
    coe
      (let v2 = coe du_setoid_108 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe d_isEquivalence_60 (coe v2)) v3))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.setoid
d_setoid_752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 -> T_Setoid_44
d_setoid_752 ~v0 ~v1 ~v2 v3 = du_setoid_752 v3
du_setoid_752 :: T_DecStrictPartialOrder_638 -> T_Setoid_44
du_setoid_752 v0
  = coe du_setoid_108 (coe du_decSetoid_728 (coe v0))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.sym
d_sym_754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_754 ~v0 ~v1 ~v2 v3 = du_sym_754 v3
du_sym_754 ::
  T_DecStrictPartialOrder_638 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_754 v0
  = let v1 = coe du_decSetoid_728 (coe v0) in
    coe
      (let v2 = coe du_setoid_108 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.DecStrictPartialOrder.Eq._.trans
d_trans_756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecStrictPartialOrder_638 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_756 ~v0 ~v1 ~v2 v3 = du_trans_756 v3
du_trans_756 ::
  T_DecStrictPartialOrder_638 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_756 v0
  = let v1 = coe du_decSetoid_728 (coe v0) in
    coe
      (let v2 = coe du_setoid_108 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe d_isEquivalence_60 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder
d_TotalOrder_764 a0 a1 a2 = ()
newtype T_TotalOrder_764
  = C_TotalOrder'46'constructor_15747 MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
-- Relation.Binary.Bundles.TotalOrder.Carrier
d_Carrier_780 :: T_TotalOrder_764 -> ()
d_Carrier_780 = erased
-- Relation.Binary.Bundles.TotalOrder._≈_
d__'8776'__782 :: T_TotalOrder_764 -> AgdaAny -> AgdaAny -> ()
d__'8776'__782 = erased
-- Relation.Binary.Bundles.TotalOrder._≤_
d__'8804'__784 :: T_TotalOrder_764 -> AgdaAny -> AgdaAny -> ()
d__'8804'__784 = erased
-- Relation.Binary.Bundles.TotalOrder.isTotalOrder
d_isTotalOrder_786 ::
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_isTotalOrder_786 v0
  = case coe v0 of
      C_TotalOrder'46'constructor_15747 v4 -> coe v4
      _                                    -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.TotalOrder._.isPartialOrder
d_isPartialOrder_790 ::
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_790 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
      (coe d_isTotalOrder_786 (coe v0))
-- Relation.Binary.Bundles.TotalOrder._.isTotalPreorder
d_isTotalPreorder_792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
d_isTotalPreorder_792 ~v0 ~v1 ~v2 v3 = du_isTotalPreorder_792 v3
du_isTotalPreorder_792 ::
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
du_isTotalPreorder_792 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isTotalPreorder_454
      (coe d_isTotalOrder_786 (coe v0))
-- Relation.Binary.Bundles.TotalOrder._.total
d_total_794 ::
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_794 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_total_414
      (coe d_isTotalOrder_786 (coe v0))
-- Relation.Binary.Bundles.TotalOrder.poset
d_poset_796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> T_Poset_314
d_poset_796 ~v0 ~v1 ~v2 v3 = du_poset_796 v3
du_poset_796 :: T_TotalOrder_764 -> T_Poset_314
du_poset_796 v0
  = coe
      C_Poset'46'constructor_6389
      (MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
         (coe d_isTotalOrder_786 (coe v0)))
-- Relation.Binary.Bundles.TotalOrder._._∼_
d__'8764'__800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> AgdaAny -> AgdaAny -> ()
d__'8764'__800 = erased
-- Relation.Binary.Bundles.TotalOrder._._≳_
d__'8819'__802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> AgdaAny -> AgdaAny -> ()
d__'8819'__802 = erased
-- Relation.Binary.Bundles.TotalOrder._._⋦_
d__'8934'__804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> AgdaAny -> AgdaAny -> ()
d__'8934'__804 = erased
-- Relation.Binary.Bundles.TotalOrder._._⋧_
d__'8935'__806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> AgdaAny -> AgdaAny -> ()
d__'8935'__806 = erased
-- Relation.Binary.Bundles.TotalOrder._.antisym
d_antisym_808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_808 ~v0 ~v1 ~v2 v3 = du_antisym_808 v3
du_antisym_808 ::
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_808 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
         (coe d_isTotalOrder_786 (coe v0)))
-- Relation.Binary.Bundles.TotalOrder._.isEquivalence
d_isEquivalence_810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_810 ~v0 ~v1 ~v2 v3 = du_isEquivalence_810 v3
du_isEquivalence_810 ::
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_810 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_336 (coe v1))))
-- Relation.Binary.Bundles.TotalOrder._.isPreorder
d_isPreorder_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_812 ~v0 ~v1 ~v2 v3 = du_isPreorder_812 v3
du_isPreorder_812 ::
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder_812 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
         (coe d_isTotalOrder_786 (coe v0)))
-- Relation.Binary.Bundles.TotalOrder._.preorder
d_preorder_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> T_Preorder_132
d_preorder_814 ~v0 ~v1 ~v2 v3 = du_preorder_814 v3
du_preorder_814 :: T_TotalOrder_764 -> T_Preorder_132
du_preorder_814 v0
  = coe du_preorder_344 (coe du_poset_796 (coe v0))
-- Relation.Binary.Bundles.TotalOrder._.refl
d_refl_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> AgdaAny -> AgdaAny
d_refl_816 ~v0 ~v1 ~v2 v3 = du_refl_816 v3
du_refl_816 :: T_TotalOrder_764 -> AgdaAny -> AgdaAny
du_refl_816 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.reflexive
d_reflexive_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_818 ~v0 ~v1 ~v2 v3 = du_reflexive_818 v3
du_reflexive_818 ::
  T_TotalOrder_764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_818 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_336 (coe v1))))
-- Relation.Binary.Bundles.TotalOrder._.trans
d_trans_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_820 ~v0 ~v1 ~v2 v3 = du_trans_820 v3
du_trans_820 ::
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_820 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_84
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_336 (coe v1))))
-- Relation.Binary.Bundles.TotalOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_822 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_822 v3
du_'8764''45'resp'45''8776'_822 ::
  T_TotalOrder_764 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_822 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_824 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_824 v3
du_'8764''45'resp'691''45''8776'_824 ::
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_824 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_826 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_826 v3
du_'8764''45'resp'737''45''8776'_826 ::
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_826 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_828 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_828 v3
du_'8818''45'resp'45''8776'_828 ::
  T_TotalOrder_764 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_828 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_830 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_830 v3
du_'8818''45'resp'691''45''8776'_830 ::
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_830 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_832 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_832 v3
du_'8818''45'resp'737''45''8776'_832 ::
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_832 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.Eq._≈_
d__'8776'__836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> AgdaAny -> AgdaAny -> ()
d__'8776'__836 = erased
-- Relation.Binary.Bundles.TotalOrder._.Eq._≉_
d__'8777'__838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> AgdaAny -> AgdaAny -> ()
d__'8777'__838 = erased
-- Relation.Binary.Bundles.TotalOrder._.Eq.Carrier
d_Carrier_840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_TotalOrder_764 -> ()
d_Carrier_840 = erased
-- Relation.Binary.Bundles.TotalOrder._.Eq.isEquivalence
d_isEquivalence_842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_842 ~v0 ~v1 ~v2 v3 = du_isEquivalence_842 v3
du_isEquivalence_842 ::
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_842 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe d_isPreorder_154 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_844 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_844 v3
du_isPartialEquivalence_844 ::
  T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_844 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (let v3 = coe du_setoid_180 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_60 (coe v3)))))
-- Relation.Binary.Bundles.TotalOrder._.Eq.partialSetoid
d_partialSetoid_846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> T_PartialSetoid_10
d_partialSetoid_846 ~v0 ~v1 ~v2 v3 = du_partialSetoid_846 v3
du_partialSetoid_846 :: T_TotalOrder_764 -> T_PartialSetoid_10
du_partialSetoid_846 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe (coe du_partialSetoid_70 (coe du_setoid_180 (coe v2))))
-- Relation.Binary.Bundles.TotalOrder._.Eq.refl
d_refl_848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> AgdaAny -> AgdaAny
d_refl_848 ~v0 ~v1 ~v2 v3 = du_refl_848 v3
du_refl_848 :: T_TotalOrder_764 -> AgdaAny -> AgdaAny
du_refl_848 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
               (coe d_isPreorder_154 (coe v2)))))
-- Relation.Binary.Bundles.TotalOrder._.Eq.reflexive
d_reflexive_850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_850 ~v0 ~v1 ~v2 v3 = du_reflexive_850 v3
du_reflexive_850 ::
  T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_850 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (let v3 = coe du_setoid_180 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_60 (coe v3)) v4)))
-- Relation.Binary.Bundles.TotalOrder._.Eq.setoid
d_setoid_852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> T_Setoid_44
d_setoid_852 ~v0 ~v1 ~v2 v3 = du_setoid_852 v3
du_setoid_852 :: T_TotalOrder_764 -> T_Setoid_44
du_setoid_852 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe (coe du_setoid_180 (coe du_preorder_344 (coe v1)))
-- Relation.Binary.Bundles.TotalOrder._.Eq.sym
d_sym_854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_854 ~v0 ~v1 ~v2 v3 = du_sym_854 v3
du_sym_854 ::
  T_TotalOrder_764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_854 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (let v3 = coe du_setoid_180 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe d_isEquivalence_60 (coe v3)))))
-- Relation.Binary.Bundles.TotalOrder._.Eq.trans
d_trans_856 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_856 ~v0 ~v1 ~v2 v3 = du_trans_856 v3
du_trans_856 ::
  T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_856 v0
  = let v1 = coe du_poset_796 (coe v0) in
    coe
      (let v2 = coe du_preorder_344 (coe v1) in
       coe
         (let v3 = coe du_setoid_180 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe d_isEquivalence_60 (coe v3)))))
-- Relation.Binary.Bundles.TotalOrder.totalPreorder
d_totalPreorder_858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_TotalOrder_764 -> T_TotalPreorder_222
d_totalPreorder_858 ~v0 ~v1 ~v2 v3 = du_totalPreorder_858 v3
du_totalPreorder_858 :: T_TotalOrder_764 -> T_TotalPreorder_222
du_totalPreorder_858 v0
  = coe
      C_TotalPreorder'46'constructor_4573
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isTotalPreorder_454
         (coe d_isTotalOrder_786 (coe v0)))
-- Relation.Binary.Bundles.DecTotalOrder
d_DecTotalOrder_866 a0 a1 a2 = ()
newtype T_DecTotalOrder_866
  = C_DecTotalOrder'46'constructor_17849 MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
-- Relation.Binary.Bundles.DecTotalOrder.Carrier
d_Carrier_882 :: T_DecTotalOrder_866 -> ()
d_Carrier_882 = erased
-- Relation.Binary.Bundles.DecTotalOrder._≈_
d__'8776'__884 :: T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> ()
d__'8776'__884 = erased
-- Relation.Binary.Bundles.DecTotalOrder._≤_
d__'8804'__886 :: T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> ()
d__'8804'__886 = erased
-- Relation.Binary.Bundles.DecTotalOrder.isDecTotalOrder
d_isDecTotalOrder_888 ::
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_isDecTotalOrder_888 v0
  = case coe v0 of
      C_DecTotalOrder'46'constructor_17849 v4 -> coe v4
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.DecTotalOrder.DTO._≟_
d__'8799'__892 ::
  T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__892 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8799'__472
      (coe d_isDecTotalOrder_888 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder.DTO._≤?_
d__'8804''63'__894 ::
  T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__894 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__474
      (coe d_isDecTotalOrder_888 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder.DTO.isDecPartialOrder
d_isDecPartialOrder_898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
d_isDecPartialOrder_898 ~v0 ~v1 ~v2 v3
  = du_isDecPartialOrder_898 v3
du_isDecPartialOrder_898 ::
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
du_isDecPartialOrder_898 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isDecPartialOrder_508
      (coe d_isDecTotalOrder_888 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder.DTO.isTotalOrder
d_isTotalOrder_906 ::
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_isTotalOrder_906 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_470
      (coe d_isDecTotalOrder_888 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder.totalOrder
d_totalOrder_948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> T_TotalOrder_764
d_totalOrder_948 ~v0 ~v1 ~v2 v3 = du_totalOrder_948 v3
du_totalOrder_948 :: T_DecTotalOrder_866 -> T_TotalOrder_764
du_totalOrder_948 v0
  = coe
      C_TotalOrder'46'constructor_15747
      (MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_470
         (coe d_isDecTotalOrder_888 (coe v0)))
-- Relation.Binary.Bundles.DecTotalOrder._._∼_
d__'8764'__952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> ()
d__'8764'__952 = erased
-- Relation.Binary.Bundles.DecTotalOrder._._≳_
d__'8819'__954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> ()
d__'8819'__954 = erased
-- Relation.Binary.Bundles.DecTotalOrder._._⋦_
d__'8934'__956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> ()
d__'8934'__956 = erased
-- Relation.Binary.Bundles.DecTotalOrder._._⋧_
d__'8935'__958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> ()
d__'8935'__958 = erased
-- Relation.Binary.Bundles.DecTotalOrder._.antisym
d_antisym_960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_960 ~v0 ~v1 ~v2 v3 = du_antisym_960 v3
du_antisym_960 ::
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_960 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
            (coe d_isTotalOrder_786 (coe v1))))
-- Relation.Binary.Bundles.DecTotalOrder._.isEquivalence
d_isEquivalence_962 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_962 ~v0 ~v1 ~v2 v3 = du_isEquivalence_962 v3
du_isEquivalence_962 ::
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_962 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (let v2 = coe du_poset_796 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe d_isPartialOrder_336 (coe v2)))))
-- Relation.Binary.Bundles.DecTotalOrder._.isPartialOrder
d_isPartialOrder_964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_964 ~v0 ~v1 ~v2 v3 = du_isPartialOrder_964 v3
du_isPartialOrder_964 ::
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_isPartialOrder_964 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_470
         (coe d_isDecTotalOrder_888 (coe v0)))
-- Relation.Binary.Bundles.DecTotalOrder._.isPreorder
d_isPreorder_966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_966 ~v0 ~v1 ~v2 v3 = du_isPreorder_966 v3
du_isPreorder_966 ::
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder_966 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
            (coe d_isTotalOrder_786 (coe v1))))
-- Relation.Binary.Bundles.DecTotalOrder._.isTotalPreorder
d_isTotalPreorder_968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
d_isTotalPreorder_968 ~v0 ~v1 ~v2 v3 = du_isTotalPreorder_968 v3
du_isTotalPreorder_968 ::
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
du_isTotalPreorder_968 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isTotalPreorder_454
         (coe d_isTotalOrder_786 (coe v1)))
-- Relation.Binary.Bundles.DecTotalOrder._.poset
d_poset_970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> T_Poset_314
d_poset_970 ~v0 ~v1 ~v2 v3 = du_poset_970 v3
du_poset_970 :: T_DecTotalOrder_866 -> T_Poset_314
du_poset_970 v0 = coe du_poset_796 (coe du_totalOrder_948 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder._.preorder
d_preorder_972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> T_Preorder_132
d_preorder_972 ~v0 ~v1 ~v2 v3 = du_preorder_972 v3
du_preorder_972 :: T_DecTotalOrder_866 -> T_Preorder_132
du_preorder_972 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe (coe du_preorder_344 (coe du_poset_796 (coe v1)))
-- Relation.Binary.Bundles.DecTotalOrder._.refl
d_refl_974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny
d_refl_974 ~v0 ~v1 ~v2 v3 = du_refl_974 v3
du_refl_974 :: T_DecTotalOrder_866 -> AgdaAny -> AgdaAny
du_refl_974 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (let v2 = coe du_poset_796 (coe v1) in
       coe
         (let v3 = coe du_preorder_344 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_98
               (coe d_isPreorder_154 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.reflexive
d_reflexive_976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_976 ~v0 ~v1 ~v2 v3 = du_reflexive_976 v3
du_reflexive_976 ::
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_976 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (let v2 = coe du_poset_796 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe d_isPartialOrder_336 (coe v2)))))
-- Relation.Binary.Bundles.DecTotalOrder._.total
d_total_978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_978 ~v0 ~v1 ~v2 v3 = du_total_978 v3
du_total_978 ::
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_total_978 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_total_414
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_470
         (coe d_isDecTotalOrder_888 (coe v0)))
-- Relation.Binary.Bundles.DecTotalOrder._.totalPreorder
d_totalPreorder_980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> T_TotalPreorder_222
d_totalPreorder_980 ~v0 ~v1 ~v2 v3 = du_totalPreorder_980 v3
du_totalPreorder_980 :: T_DecTotalOrder_866 -> T_TotalPreorder_222
du_totalPreorder_980 v0
  = coe du_totalPreorder_858 (coe du_totalOrder_948 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder._.trans
d_trans_982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_982 ~v0 ~v1 ~v2 v3 = du_trans_982 v3
du_trans_982 ::
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_982 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (let v2 = coe du_poset_796 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_84
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe d_isPartialOrder_336 (coe v2)))))
-- Relation.Binary.Bundles.DecTotalOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_984 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_984 v3
du_'8764''45'resp'45''8776'_984 ::
  T_DecTotalOrder_866 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_984 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (let v2 = coe du_poset_796 (coe v1) in
       coe
         (let v3 = coe du_preorder_344 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
               (coe d_isPreorder_154 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_986 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_986 v3
du_'8764''45'resp'691''45''8776'_986 ::
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_986 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (let v2 = coe du_poset_796 (coe v1) in
       coe
         (let v3 = coe du_preorder_344 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
               (coe d_isPreorder_154 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_988 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_988 v3
du_'8764''45'resp'737''45''8776'_988 ::
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_988 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (let v2 = coe du_poset_796 (coe v1) in
       coe
         (let v3 = coe du_preorder_344 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
               (coe d_isPreorder_154 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_990 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_990 v3
du_'8818''45'resp'45''8776'_990 ::
  T_DecTotalOrder_866 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_990 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (let v2 = coe du_poset_796 (coe v1) in
       coe
         (let v3 = coe du_preorder_344 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
               (coe d_isPreorder_154 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_992 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_992 v3
du_'8818''45'resp'691''45''8776'_992 ::
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_992 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (let v2 = coe du_poset_796 (coe v1) in
       coe
         (let v3 = coe du_preorder_344 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
               (coe d_isPreorder_154 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_994 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_994 v3
du_'8818''45'resp'737''45''8776'_994 ::
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_994 v0
  = let v1 = coe du_totalOrder_948 (coe v0) in
    coe
      (let v2 = coe du_poset_796 (coe v1) in
       coe
         (let v3 = coe du_preorder_344 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
               (coe d_isPreorder_154 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder.decPoset
d_decPoset_996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> T_DecPoset_406
d_decPoset_996 ~v0 ~v1 ~v2 v3 = du_decPoset_996 v3
du_decPoset_996 :: T_DecTotalOrder_866 -> T_DecPoset_406
du_decPoset_996 v0
  = coe
      C_DecPoset'46'constructor_8213
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecPartialOrder_508
         (coe d_isDecTotalOrder_888 (coe v0)))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq._≈_
d__'8776'__1002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1002 = erased
-- Relation.Binary.Bundles.DecTotalOrder._.Eq._≉_
d__'8777'__1004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1004 = erased
-- Relation.Binary.Bundles.DecTotalOrder._.Eq._≟_
d__'8799'__1006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__1006 ~v0 ~v1 ~v2 v3 = du__'8799'__1006 v3
du__'8799'__1006 ::
  T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__1006 v0
  = let v1 = coe du_decPoset_996 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__236
         (coe d_isDecPartialOrder_428 (coe v1)))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.Carrier
d_Carrier_1008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_DecTotalOrder_866 -> ()
d_Carrier_1008 = erased
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.decSetoid
d_decSetoid_1010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> T_DecSetoid_84
d_decSetoid_1010 ~v0 ~v1 ~v2 v3 = du_decSetoid_1010 v3
du_decSetoid_1010 :: T_DecTotalOrder_866 -> T_DecSetoid_84
du_decSetoid_1010 v0
  = coe du_decSetoid_520 (coe du_decPoset_996 (coe v0))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.isDecEquivalence
d_isDecEquivalence_1012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_1012 ~v0 ~v1 ~v2 v3
  = du_isDecEquivalence_1012 v3
du_isDecEquivalence_1012 ::
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_isDecEquivalence_1012 v0
  = let v1 = coe du_decPoset_996 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_268
         (coe d_isDecPartialOrder_428 (coe v1)))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.isEquivalence
d_isEquivalence_1014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1014 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1014 v3
du_isEquivalence_1014 ::
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1014 v0
  = let v1 = coe du_decPoset_996 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_234
               (coe d_isDecPartialOrder_428 (coe v1)))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_1016 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1016 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1016 v3
du_isPartialEquivalence_1016 ::
  T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1016 v0
  = let v1 = coe du_decPoset_996 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_520 (coe v1) in
       coe
         (let v3 = coe du_setoid_108 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_60 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.partialSetoid
d_partialSetoid_1018 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> T_PartialSetoid_10
d_partialSetoid_1018 ~v0 ~v1 ~v2 v3 = du_partialSetoid_1018 v3
du_partialSetoid_1018 :: T_DecTotalOrder_866 -> T_PartialSetoid_10
du_partialSetoid_1018 v0
  = let v1 = coe du_decPoset_996 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_520 (coe v1) in
       coe (coe du_partialSetoid_70 (coe du_setoid_108 (coe v2))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.refl
d_refl_1020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny
d_refl_1020 ~v0 ~v1 ~v2 v3 = du_refl_1020 v3
du_refl_1020 :: T_DecTotalOrder_866 -> AgdaAny -> AgdaAny
du_refl_1020 v0
  = let v1 = coe du_decPoset_996 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_520 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
               (coe d_isDecEquivalence_100 (coe v2)))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.reflexive
d_reflexive_1022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1022 ~v0 ~v1 ~v2 v3 = du_reflexive_1022 v3
du_reflexive_1022 ::
  T_DecTotalOrder_866 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1022 v0
  = let v1 = coe du_decPoset_996 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_520 (coe v1) in
       coe
         (let v3 = coe du_setoid_108 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_60 (coe v3)) v4)))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.setoid
d_setoid_1024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> T_Setoid_44
d_setoid_1024 ~v0 ~v1 ~v2 v3 = du_setoid_1024 v3
du_setoid_1024 :: T_DecTotalOrder_866 -> T_Setoid_44
du_setoid_1024 v0
  = let v1 = coe du_decPoset_996 (coe v0) in
    coe (coe du_setoid_108 (coe du_decSetoid_520 (coe v1)))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.sym
d_sym_1026 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1026 ~v0 ~v1 ~v2 v3 = du_sym_1026 v3
du_sym_1026 ::
  T_DecTotalOrder_866 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1026 v0
  = let v1 = coe du_decPoset_996 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_520 (coe v1) in
       coe
         (let v3 = coe du_setoid_108 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe d_isEquivalence_60 (coe v3)))))
-- Relation.Binary.Bundles.DecTotalOrder._.Eq.trans
d_trans_1028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1028 ~v0 ~v1 ~v2 v3 = du_trans_1028 v3
du_trans_1028 ::
  T_DecTotalOrder_866 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1028 v0
  = let v1 = coe du_decPoset_996 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_520 (coe v1) in
       coe
         (let v3 = coe du_setoid_108 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe d_isEquivalence_60 (coe v3)))))
-- Relation.Binary.Bundles.StrictTotalOrder
d_StrictTotalOrder_1036 a0 a1 a2 = ()
newtype T_StrictTotalOrder_1036
  = C_StrictTotalOrder'46'constructor_21059 MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
-- Relation.Binary.Bundles.StrictTotalOrder.Carrier
d_Carrier_1052 :: T_StrictTotalOrder_1036 -> ()
d_Carrier_1052 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._≈_
d__'8776'__1054 ::
  T_StrictTotalOrder_1036 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1054 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._<_
d__'60'__1056 ::
  T_StrictTotalOrder_1036 -> AgdaAny -> AgdaAny -> ()
d__'60'__1056 = erased
-- Relation.Binary.Bundles.StrictTotalOrder.isStrictTotalOrder
d_isStrictTotalOrder_1058 ::
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_isStrictTotalOrder_1058 v0
  = case coe v0 of
      C_StrictTotalOrder'46'constructor_21059 v4 -> coe v4
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.StrictTotalOrder._._<?_
d__'60''63'__1062 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__1062 ~v0 ~v1 ~v2 v3 = du__'60''63'__1062 v3
du__'60''63'__1062 ::
  T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'60''63'__1062 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du__'60''63'__564
      (coe d_isStrictTotalOrder_1058 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._._≟_
d__'8799'__1064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__1064 ~v0 ~v1 ~v2 v3 = du__'8799'__1064 v3
du__'8799'__1064 ::
  T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__1064 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du__'8799'__562
      (coe d_isStrictTotalOrder_1058 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._.compare
d_compare_1066 ::
  T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_1066 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_compare_544
      (coe d_isStrictTotalOrder_1058 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._.isDecEquivalence
d_isDecEquivalence_1068 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_1068 ~v0 ~v1 ~v2 v3
  = du_isDecEquivalence_1068 v3
du_isDecEquivalence_1068 ::
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_isDecEquivalence_1068 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_588
      (coe d_isStrictTotalOrder_1058 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._.isDecStrictPartialOrder
d_isDecStrictPartialOrder_1070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
d_isDecStrictPartialOrder_1070 ~v0 ~v1 ~v2 v3
  = du_isDecStrictPartialOrder_1070 v3
du_isDecStrictPartialOrder_1070 ::
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
du_isDecStrictPartialOrder_1070 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isDecStrictPartialOrder_566
      (coe d_isStrictTotalOrder_1058 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._.isStrictPartialOrder
d_isStrictPartialOrder_1072 ::
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_isStrictPartialOrder_1072 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
      (coe d_isStrictTotalOrder_1058 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder.strictPartialOrder
d_strictPartialOrder_1074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> T_StrictPartialOrder_556
d_strictPartialOrder_1074 ~v0 ~v1 ~v2 v3
  = du_strictPartialOrder_1074 v3
du_strictPartialOrder_1074 ::
  T_StrictTotalOrder_1036 -> T_StrictPartialOrder_556
du_strictPartialOrder_1074 v0
  = coe
      C_StrictPartialOrder'46'constructor_11097
      (MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
         (coe d_isStrictTotalOrder_1058 (coe v0)))
-- Relation.Binary.Bundles.StrictTotalOrder._._>_
d__'62'__1078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> AgdaAny -> AgdaAny -> ()
d__'62'__1078 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._._≮_
d__'8814'__1080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> AgdaAny -> AgdaAny -> ()
d__'8814'__1080 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._._≯_
d__'8815'__1082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> AgdaAny -> AgdaAny -> ()
d__'8815'__1082 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.<-resp-≈
d_'60''45'resp'45''8776'_1084 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_1084 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_1084 v3
du_'60''45'resp'45''8776'_1084 ::
  T_StrictTotalOrder_1036 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_1084 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
         (coe d_isStrictTotalOrder_1058 (coe v0)))
-- Relation.Binary.Bundles.StrictTotalOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_1086 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_1086 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_1086 v3
du_'60''45'resp'691''45''8776'_1086 ::
  T_StrictTotalOrder_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_1086 v0
  = let v1 = coe du_strictPartialOrder_1074 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_328
         (coe d_isStrictPartialOrder_578 (coe v1)))
-- Relation.Binary.Bundles.StrictTotalOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_1088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_1088 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_1088 v3
du_'60''45'resp'737''45''8776'_1088 ::
  T_StrictTotalOrder_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_1088 v0
  = let v1 = coe du_strictPartialOrder_1074 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_330
         (coe d_isStrictPartialOrder_578 (coe v1)))
-- Relation.Binary.Bundles.StrictTotalOrder._.asym
d_asym_1090 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_1090 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.irrefl
d_irrefl_1092 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_1092 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.isEquivalence
d_isEquivalence_1094 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1094 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1094 v3
du_isEquivalence_1094 ::
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1094 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
         (coe d_isStrictTotalOrder_1058 (coe v0)))
-- Relation.Binary.Bundles.StrictTotalOrder._.trans
d_trans_1096 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1096 ~v0 ~v1 ~v2 v3 = du_trans_1096 v3
du_trans_1096 ::
  T_StrictTotalOrder_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1096 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_306
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
         (coe d_isStrictTotalOrder_1058 (coe v0)))
-- Relation.Binary.Bundles.StrictTotalOrder.decStrictPartialOrder
d_decStrictPartialOrder_1098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> T_DecStrictPartialOrder_638
d_decStrictPartialOrder_1098 ~v0 ~v1 ~v2 v3
  = du_decStrictPartialOrder_1098 v3
du_decStrictPartialOrder_1098 ::
  T_StrictTotalOrder_1036 -> T_DecStrictPartialOrder_638
du_decStrictPartialOrder_1098 v0
  = coe
      C_DecStrictPartialOrder'46'constructor_13245
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecStrictPartialOrder_566
         (coe d_isStrictTotalOrder_1058 (coe v0)))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq._≈_
d__'8776'__1104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1104 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq._≉_
d__'8777'__1106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1106 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq._≟_
d__'8799'__1108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__1108 ~v0 ~v1 ~v2 v3 = du__'8799'__1108 v3
du__'8799'__1108 ::
  T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__1108 v0
  = let v1 = coe du_decStrictPartialOrder_1098 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__348
         (coe d_isDecStrictPartialOrder_660 (coe v1)))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.Carrier
d_Carrier_1110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> ()
d_Carrier_1110 = erased
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.decSetoid
d_decSetoid_1112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> T_DecSetoid_84
d_decSetoid_1112 ~v0 ~v1 ~v2 v3 = du_decSetoid_1112 v3
du_decSetoid_1112 :: T_StrictTotalOrder_1036 -> T_DecSetoid_84
du_decSetoid_1112 v0
  = coe du_decSetoid_728 (coe du_decStrictPartialOrder_1098 (coe v0))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.isDecEquivalence
d_isDecEquivalence_1114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_1114 ~v0 ~v1 ~v2 v3
  = du_isDecEquivalence_1114 v3
du_isDecEquivalence_1114 ::
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_isDecEquivalence_1114 v0
  = let v1 = coe du_decStrictPartialOrder_1098 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_382
         (coe d_isDecStrictPartialOrder_660 (coe v1)))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.isEquivalence
d_isEquivalence_1116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1116 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1116 v3
du_isEquivalence_1116 ::
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1116 v0
  = let v1 = coe du_decStrictPartialOrder_1098 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
            (coe d_isDecStrictPartialOrder_660 (coe v1))))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_1118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1118 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1118 v3
du_isPartialEquivalence_1118 ::
  T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1118 v0
  = let v1 = coe du_decStrictPartialOrder_1098 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_728 (coe v1) in
       coe
         (let v3 = coe du_setoid_108 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_isEquivalence_60 (coe v3)))))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.partialSetoid
d_partialSetoid_1120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> T_PartialSetoid_10
d_partialSetoid_1120 ~v0 ~v1 ~v2 v3 = du_partialSetoid_1120 v3
du_partialSetoid_1120 ::
  T_StrictTotalOrder_1036 -> T_PartialSetoid_10
du_partialSetoid_1120 v0
  = let v1 = coe du_decStrictPartialOrder_1098 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_728 (coe v1) in
       coe (coe du_partialSetoid_70 (coe du_setoid_108 (coe v2))))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.refl
d_refl_1122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> AgdaAny -> AgdaAny
d_refl_1122 ~v0 ~v1 ~v2 v3 = du_refl_1122 v3
du_refl_1122 :: T_StrictTotalOrder_1036 -> AgdaAny -> AgdaAny
du_refl_1122 v0
  = let v1 = coe du_decStrictPartialOrder_1098 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_728 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
               (coe d_isDecEquivalence_100 (coe v2)))))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.reflexive
d_reflexive_1124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1124 ~v0 ~v1 ~v2 v3 = du_reflexive_1124 v3
du_reflexive_1124 ::
  T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1124 v0
  = let v1 = coe du_decStrictPartialOrder_1098 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_728 (coe v1) in
       coe
         (let v3 = coe du_setoid_108 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_isEquivalence_60 (coe v3)) v4)))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.setoid
d_setoid_1126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> T_Setoid_44
d_setoid_1126 ~v0 ~v1 ~v2 v3 = du_setoid_1126 v3
du_setoid_1126 :: T_StrictTotalOrder_1036 -> T_Setoid_44
du_setoid_1126 v0
  = let v1 = coe du_decStrictPartialOrder_1098 (coe v0) in
    coe (coe du_setoid_108 (coe du_decSetoid_728 (coe v1)))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.sym
d_sym_1128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1128 ~v0 ~v1 ~v2 v3 = du_sym_1128 v3
du_sym_1128 ::
  T_StrictTotalOrder_1036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1128 v0
  = let v1 = coe du_decStrictPartialOrder_1098 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_728 (coe v1) in
       coe
         (let v3 = coe du_setoid_108 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe d_isEquivalence_60 (coe v3)))))
-- Relation.Binary.Bundles.StrictTotalOrder._.Eq.trans
d_trans_1130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1130 ~v0 ~v1 ~v2 v3 = du_trans_1130 v3
du_trans_1130 ::
  T_StrictTotalOrder_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1130 v0
  = let v1 = coe du_decStrictPartialOrder_1098 (coe v0) in
    coe
      (let v2 = coe du_decSetoid_728 (coe v1) in
       coe
         (let v3 = coe du_setoid_108 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe d_isEquivalence_60 (coe v3)))))
-- Relation.Binary.Bundles.StrictTotalOrder.decSetoid
d_decSetoid_1132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_StrictTotalOrder_1036 -> T_DecSetoid_84
d_decSetoid_1132 ~v0 ~v1 ~v2 v3 = du_decSetoid_1132 v3
du_decSetoid_1132 :: T_StrictTotalOrder_1036 -> T_DecSetoid_84
du_decSetoid_1132 v0
  = coe du_decSetoid_728 (coe du_decStrictPartialOrder_1098 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder
d_DenseLinearOrder_1140 a0 a1 a2 = ()
newtype T_DenseLinearOrder_1140
  = C_DenseLinearOrder'46'constructor_23325 MAlonzo.Code.Relation.Binary.Structures.T_IsDenseLinearOrder_594
-- Relation.Binary.Bundles.DenseLinearOrder.Carrier
d_Carrier_1156 :: T_DenseLinearOrder_1140 -> ()
d_Carrier_1156 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._≈_
d__'8776'__1158 ::
  T_DenseLinearOrder_1140 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1158 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._<_
d__'60'__1160 ::
  T_DenseLinearOrder_1140 -> AgdaAny -> AgdaAny -> ()
d__'60'__1160 = erased
-- Relation.Binary.Bundles.DenseLinearOrder.isDenseLinearOrder
d_isDenseLinearOrder_1162 ::
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDenseLinearOrder_594
d_isDenseLinearOrder_1162 v0
  = case coe v0 of
      C_DenseLinearOrder'46'constructor_23325 v4 -> coe v4
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.DenseLinearOrder._.dense
d_dense_1166 ::
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dense_1166 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_dense_604
      (coe d_isDenseLinearOrder_1162 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder._.isStrictTotalOrder
d_isStrictTotalOrder_1168 ::
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_isStrictTotalOrder_1168 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isStrictTotalOrder_602
      (coe d_isDenseLinearOrder_1162 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder.strictTotalOrder
d_strictTotalOrder_1170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> T_StrictTotalOrder_1036
d_strictTotalOrder_1170 ~v0 ~v1 ~v2 v3
  = du_strictTotalOrder_1170 v3
du_strictTotalOrder_1170 ::
  T_DenseLinearOrder_1140 -> T_StrictTotalOrder_1036
du_strictTotalOrder_1170 v0
  = coe
      C_StrictTotalOrder'46'constructor_21059
      (MAlonzo.Code.Relation.Binary.Structures.d_isStrictTotalOrder_602
         (coe d_isDenseLinearOrder_1162 (coe v0)))
-- Relation.Binary.Bundles.DenseLinearOrder._._<?_
d__'60''63'__1174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__1174 ~v0 ~v1 ~v2 v3 = du__'60''63'__1174 v3
du__'60''63'__1174 ::
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'60''63'__1174 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du__'60''63'__564
         (coe d_isStrictTotalOrder_1058 (coe v1)))
-- Relation.Binary.Bundles.DenseLinearOrder._._>_
d__'62'__1176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> AgdaAny -> AgdaAny -> ()
d__'62'__1176 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._._≟_
d__'8799'__1178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__1178 ~v0 ~v1 ~v2 v3 = du__'8799'__1178 v3
du__'8799'__1178 ::
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__1178 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du__'8799'__562
         (coe d_isStrictTotalOrder_1058 (coe v1)))
-- Relation.Binary.Bundles.DenseLinearOrder._._≮_
d__'8814'__1180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> AgdaAny -> AgdaAny -> ()
d__'8814'__1180 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._._≯_
d__'8815'__1182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> AgdaAny -> AgdaAny -> ()
d__'8815'__1182 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.<-resp-≈
d_'60''45'resp'45''8776'_1184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_1184 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'45''8776'_1184 v3
du_'60''45'resp'45''8776'_1184 ::
  T_DenseLinearOrder_1140 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_1184 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe d_isStrictTotalOrder_1058 (coe v1))))
-- Relation.Binary.Bundles.DenseLinearOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_1186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_1186 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'691''45''8776'_1186 v3
du_'60''45'resp'691''45''8776'_1186 ::
  T_DenseLinearOrder_1140 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_1186 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_strictPartialOrder_1074 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'691''45''8776'_328
            (coe d_isStrictPartialOrder_578 (coe v2))))
-- Relation.Binary.Bundles.DenseLinearOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_1188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_1188 ~v0 ~v1 ~v2 v3
  = du_'60''45'resp'737''45''8776'_1188 v3
du_'60''45'resp'737''45''8776'_1188 ::
  T_DenseLinearOrder_1140 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_1188 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_strictPartialOrder_1074 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'60''45'resp'737''45''8776'_330
            (coe d_isStrictPartialOrder_578 (coe v2))))
-- Relation.Binary.Bundles.DenseLinearOrder._.asym
d_asym_1190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_1190 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.compare
d_compare_1192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_1192 ~v0 ~v1 ~v2 v3 = du_compare_1192 v3
du_compare_1192 ::
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_compare_1192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_compare_544
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictTotalOrder_602
         (coe d_isDenseLinearOrder_1162 (coe v0)))
-- Relation.Binary.Bundles.DenseLinearOrder._.decSetoid
d_decSetoid_1194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> T_DecSetoid_84
d_decSetoid_1194 ~v0 ~v1 ~v2 v3 = du_decSetoid_1194 v3
du_decSetoid_1194 :: T_DenseLinearOrder_1140 -> T_DecSetoid_84
du_decSetoid_1194 v0
  = coe du_decSetoid_1132 (coe du_strictTotalOrder_1170 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder._.decStrictPartialOrder
d_decStrictPartialOrder_1196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> T_DecStrictPartialOrder_638
d_decStrictPartialOrder_1196 ~v0 ~v1 ~v2 v3
  = du_decStrictPartialOrder_1196 v3
du_decStrictPartialOrder_1196 ::
  T_DenseLinearOrder_1140 -> T_DecStrictPartialOrder_638
du_decStrictPartialOrder_1196 v0
  = coe
      du_decStrictPartialOrder_1098
      (coe du_strictTotalOrder_1170 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder._.irrefl
d_irrefl_1198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_1198 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.isDecEquivalence
d_isDecEquivalence_1200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_1200 ~v0 ~v1 ~v2 v3
  = du_isDecEquivalence_1200 v3
du_isDecEquivalence_1200 ::
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_isDecEquivalence_1200 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_588
         (coe d_isStrictTotalOrder_1058 (coe v1)))
-- Relation.Binary.Bundles.DenseLinearOrder._.isDecStrictPartialOrder
d_isDecStrictPartialOrder_1202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
d_isDecStrictPartialOrder_1202 ~v0 ~v1 ~v2 v3
  = du_isDecStrictPartialOrder_1202 v3
du_isDecStrictPartialOrder_1202 ::
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
du_isDecStrictPartialOrder_1202 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isDecStrictPartialOrder_566
         (coe d_isStrictTotalOrder_1058 (coe v1)))
-- Relation.Binary.Bundles.DenseLinearOrder._.isEquivalence
d_isEquivalence_1204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1204 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1204 v3
du_isEquivalence_1204 ::
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1204 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe d_isStrictTotalOrder_1058 (coe v1))))
-- Relation.Binary.Bundles.DenseLinearOrder._.isStrictPartialOrder
d_isStrictPartialOrder_1206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_isStrictPartialOrder_1206 ~v0 ~v1 ~v2 v3
  = du_isStrictPartialOrder_1206 v3
du_isStrictPartialOrder_1206 ::
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_isStrictPartialOrder_1206 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isStrictTotalOrder_602
         (coe d_isDenseLinearOrder_1162 (coe v0)))
-- Relation.Binary.Bundles.DenseLinearOrder._.strictPartialOrder
d_strictPartialOrder_1208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> T_StrictPartialOrder_556
d_strictPartialOrder_1208 ~v0 ~v1 ~v2 v3
  = du_strictPartialOrder_1208 v3
du_strictPartialOrder_1208 ::
  T_DenseLinearOrder_1140 -> T_StrictPartialOrder_556
du_strictPartialOrder_1208 v0
  = coe
      du_strictPartialOrder_1074 (coe du_strictTotalOrder_1170 (coe v0))
-- Relation.Binary.Bundles.DenseLinearOrder._.trans
d_trans_1210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1210 ~v0 ~v1 ~v2 v3 = du_trans_1210 v3
du_trans_1210 ::
  T_DenseLinearOrder_1140 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1210 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_306
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe d_isStrictTotalOrder_1058 (coe v1))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq._≈_
d__'8776'__1214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1214 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq._≉_
d__'8777'__1216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1216 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq._≟_
d__'8799'__1218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__1218 ~v0 ~v1 ~v2 v3 = du__'8799'__1218 v3
du__'8799'__1218 ::
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__1218 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1098 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__348
            (coe d_isDecStrictPartialOrder_660 (coe v2))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.Carrier
d_Carrier_1220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> ()
d_Carrier_1220 = erased
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.decSetoid
d_decSetoid_1222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> T_DecSetoid_84
d_decSetoid_1222 ~v0 ~v1 ~v2 v3 = du_decSetoid_1222 v3
du_decSetoid_1222 :: T_DenseLinearOrder_1140 -> T_DecSetoid_84
du_decSetoid_1222 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (coe du_decSetoid_728 (coe du_decStrictPartialOrder_1098 (coe v1)))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.isDecEquivalence
d_isDecEquivalence_1224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_1224 ~v0 ~v1 ~v2 v3
  = du_isDecEquivalence_1224 v3
du_isDecEquivalence_1224 ::
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_isDecEquivalence_1224 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1098 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isDecEquivalence_382
            (coe d_isDecStrictPartialOrder_660 (coe v2))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.isEquivalence
d_isEquivalence_1226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1226 ~v0 ~v1 ~v2 v3 = du_isEquivalence_1226 v3
du_isEquivalence_1226 ::
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1226 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1098 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
               (coe d_isDecStrictPartialOrder_660 (coe v2)))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_1228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1228 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1228 v3
du_isPartialEquivalence_1228 ::
  T_DenseLinearOrder_1140 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1228 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1098 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_728 (coe v2) in
          coe
            (let v4 = coe du_setoid_108 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe d_isEquivalence_60 (coe v4))))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.partialSetoid
d_partialSetoid_1230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> T_PartialSetoid_10
d_partialSetoid_1230 ~v0 ~v1 ~v2 v3 = du_partialSetoid_1230 v3
du_partialSetoid_1230 ::
  T_DenseLinearOrder_1140 -> T_PartialSetoid_10
du_partialSetoid_1230 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1098 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_728 (coe v2) in
          coe (coe du_partialSetoid_70 (coe du_setoid_108 (coe v3)))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.refl
d_refl_1232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> AgdaAny -> AgdaAny
d_refl_1232 ~v0 ~v1 ~v2 v3 = du_refl_1232 v3
du_refl_1232 :: T_DenseLinearOrder_1140 -> AgdaAny -> AgdaAny
du_refl_1232 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1098 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_728 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_34
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
                  (coe d_isDecEquivalence_100 (coe v3))))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.reflexive
d_reflexive_1234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1234 ~v0 ~v1 ~v2 v3 = du_reflexive_1234 v3
du_reflexive_1234 ::
  T_DenseLinearOrder_1140 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1234 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1098 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_728 (coe v2) in
          coe
            (let v4 = coe du_setoid_108 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe d_isEquivalence_60 (coe v4)) v5))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.setoid
d_setoid_1236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> T_Setoid_44
d_setoid_1236 ~v0 ~v1 ~v2 v3 = du_setoid_1236 v3
du_setoid_1236 :: T_DenseLinearOrder_1140 -> T_Setoid_44
du_setoid_1236 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1098 (coe v1) in
       coe (coe du_setoid_108 (coe du_decSetoid_728 (coe v2))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.sym
d_sym_1238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1238 ~v0 ~v1 ~v2 v3 = du_sym_1238 v3
du_sym_1238 ::
  T_DenseLinearOrder_1140 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1238 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1098 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_728 (coe v2) in
          coe
            (let v4 = coe du_setoid_108 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe d_isEquivalence_60 (coe v4))))))
-- Relation.Binary.Bundles.DenseLinearOrder._.Eq.trans
d_trans_1240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DenseLinearOrder_1140 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1240 ~v0 ~v1 ~v2 v3 = du_trans_1240 v3
du_trans_1240 ::
  T_DenseLinearOrder_1140 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1240 v0
  = let v1 = coe du_strictTotalOrder_1170 (coe v0) in
    coe
      (let v2 = coe du_decStrictPartialOrder_1098 (coe v1) in
       coe
         (let v3 = coe du_decSetoid_728 (coe v2) in
          coe
            (let v4 = coe du_setoid_108 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe d_isEquivalence_60 (coe v4))))))
-- Relation.Binary.Bundles.ApartnessRelation
d_ApartnessRelation_1248 a0 a1 a2 = ()
newtype T_ApartnessRelation_1248
  = C_ApartnessRelation'46'constructor_25337 MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_656
-- Relation.Binary.Bundles.ApartnessRelation.Carrier
d_Carrier_1264 :: T_ApartnessRelation_1248 -> ()
d_Carrier_1264 = erased
-- Relation.Binary.Bundles.ApartnessRelation._≈_
d__'8776'__1266 ::
  T_ApartnessRelation_1248 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1266 = erased
-- Relation.Binary.Bundles.ApartnessRelation._#_
d__'35'__1268 ::
  T_ApartnessRelation_1248 -> AgdaAny -> AgdaAny -> ()
d__'35'__1268 = erased
-- Relation.Binary.Bundles.ApartnessRelation.isApartnessRelation
d_isApartnessRelation_1270 ::
  T_ApartnessRelation_1248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_656
d_isApartnessRelation_1270 v0
  = case coe v0 of
      C_ApartnessRelation'46'constructor_25337 v4 -> coe v4
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Bundles.ApartnessRelation._._¬#_
d__'172''35'__1274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ApartnessRelation_1248 -> AgdaAny -> AgdaAny -> ()
d__'172''35'__1274 = erased
-- Relation.Binary.Bundles.ApartnessRelation._.cotrans
d_cotrans_1276 ::
  T_ApartnessRelation_1248 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cotrans_1276 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_cotrans_670
      (coe d_isApartnessRelation_1270 (coe v0))
-- Relation.Binary.Bundles.ApartnessRelation._.irrefl
d_irrefl_1278 ::
  T_ApartnessRelation_1248 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_1278 = erased
-- Relation.Binary.Bundles.ApartnessRelation._.sym
d_sym_1280 ::
  T_ApartnessRelation_1248 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1280 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_668
      (coe d_isApartnessRelation_1270 (coe v0))
