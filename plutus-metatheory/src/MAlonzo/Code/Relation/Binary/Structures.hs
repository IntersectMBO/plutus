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

module MAlonzo.Code.Relation.Binary.Structures where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Binary.Consequences qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Structures.IsPartialEquivalence
d_IsPartialEquivalence_16 a0 a1 a2 a3 = ()
data T_IsPartialEquivalence_16
  = C_IsPartialEquivalence'46'constructor_273 (AgdaAny ->
                                               AgdaAny -> AgdaAny -> AgdaAny)
                                              (AgdaAny ->
                                               AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Structures.IsPartialEquivalence.sym
d_sym_22 ::
  T_IsPartialEquivalence_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_22 v0
  = case coe v0 of
      C_IsPartialEquivalence'46'constructor_273 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPartialEquivalence.trans
d_trans_24 ::
  T_IsPartialEquivalence_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_24 v0
  = case coe v0 of
      C_IsPartialEquivalence'46'constructor_273 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsEquivalence
d_IsEquivalence_26 a0 a1 a2 a3 = ()
data T_IsEquivalence_26
  = C_IsEquivalence'46'constructor_745 (AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                       (AgdaAny ->
                                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Structures.IsEquivalence.refl
d_refl_34 :: T_IsEquivalence_26 -> AgdaAny -> AgdaAny
d_refl_34 v0
  = case coe v0 of
      C_IsEquivalence'46'constructor_745 v1 v2 v3 -> coe v1
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsEquivalence.sym
d_sym_36 ::
  T_IsEquivalence_26 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_36 v0
  = case coe v0 of
      C_IsEquivalence'46'constructor_745 v1 v2 v3 -> coe v2
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsEquivalence.trans
d_trans_38 ::
  T_IsEquivalence_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_38 v0
  = case coe v0 of
      C_IsEquivalence'46'constructor_745 v1 v2 v3 -> coe v3
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsEquivalence.reflexive
d_reflexive_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsEquivalence_26 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_40 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_reflexive_40 v4 v5
du_reflexive_40 :: T_IsEquivalence_26 -> AgdaAny -> AgdaAny
du_reflexive_40 v0 v1 = coe d_refl_34 v0 v1
-- Relation.Binary.Structures.IsEquivalence.isPartialEquivalence
d_isPartialEquivalence_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsEquivalence_26 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_42 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_42 v4
du_isPartialEquivalence_42 ::
  T_IsEquivalence_26 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_42 v0
  = coe
      C_IsPartialEquivalence'46'constructor_273 (coe d_sym_36 (coe v0))
      (coe d_trans_38 (coe v0))
-- Relation.Binary.Structures.IsDecEquivalence
d_IsDecEquivalence_44 a0 a1 a2 a3 = ()
data T_IsDecEquivalence_44
  = C_IsDecEquivalence'46'constructor_3083 T_IsEquivalence_26
                                           (AgdaAny ->
                                            AgdaAny ->
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
-- Relation.Binary.Structures.IsDecEquivalence.isEquivalence
d_isEquivalence_50 :: T_IsDecEquivalence_44 -> T_IsEquivalence_26
d_isEquivalence_50 v0
  = case coe v0 of
      C_IsDecEquivalence'46'constructor_3083 v1 v2 -> coe v1
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecEquivalence._≟_
d__'8799'__52 ::
  T_IsDecEquivalence_44 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__52 v0
  = case coe v0 of
      C_IsDecEquivalence'46'constructor_3083 v1 v2 -> coe v2
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecEquivalence._.isPartialEquivalence
d_isPartialEquivalence_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecEquivalence_44 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_56 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_56 v4
du_isPartialEquivalence_56 ::
  T_IsDecEquivalence_44 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_56 v0
  = coe du_isPartialEquivalence_42 (coe d_isEquivalence_50 (coe v0))
-- Relation.Binary.Structures.IsDecEquivalence._.refl
d_refl_58 :: T_IsDecEquivalence_44 -> AgdaAny -> AgdaAny
d_refl_58 v0 = coe d_refl_34 (coe d_isEquivalence_50 (coe v0))
-- Relation.Binary.Structures.IsDecEquivalence._.reflexive
d_reflexive_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecEquivalence_44 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_60 ~v0 ~v1 ~v2 ~v3 v4 = du_reflexive_60 v4
du_reflexive_60 ::
  T_IsDecEquivalence_44 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_60 v0 v1 v2 v3
  = coe du_reflexive_40 (coe d_isEquivalence_50 (coe v0)) v1
-- Relation.Binary.Structures.IsDecEquivalence._.sym
d_sym_62 ::
  T_IsDecEquivalence_44 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_62 v0 = coe d_sym_36 (coe d_isEquivalence_50 (coe v0))
-- Relation.Binary.Structures.IsDecEquivalence._.trans
d_trans_64 ::
  T_IsDecEquivalence_44 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_64 v0 = coe d_trans_38 (coe d_isEquivalence_50 (coe v0))
-- Relation.Binary.Structures.IsPreorder
d_IsPreorder_70 a0 a1 a2 a3 a4 a5 = ()
data T_IsPreorder_70
  = C_IsPreorder'46'constructor_4003 T_IsEquivalence_26
                                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                     (AgdaAny ->
                                      AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Structures.IsPreorder.isEquivalence
d_isEquivalence_80 :: T_IsPreorder_70 -> T_IsEquivalence_26
d_isEquivalence_80 v0
  = case coe v0 of
      C_IsPreorder'46'constructor_4003 v1 v2 v3 -> coe v1
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPreorder.reflexive
d_reflexive_82 ::
  T_IsPreorder_70 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_82 v0
  = case coe v0 of
      C_IsPreorder'46'constructor_4003 v1 v2 v3 -> coe v2
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPreorder.trans
d_trans_84 ::
  T_IsPreorder_70 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_84 v0
  = case coe v0 of
      C_IsPreorder'46'constructor_4003 v1 v2 v3 -> coe v3
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPreorder.Eq.isPartialEquivalence
d_isPartialEquivalence_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_70 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_88 v6
du_isPartialEquivalence_88 ::
  T_IsPreorder_70 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_88 v0
  = coe du_isPartialEquivalence_42 (coe d_isEquivalence_80 (coe v0))
-- Relation.Binary.Structures.IsPreorder.Eq.refl
d_refl_90 :: T_IsPreorder_70 -> AgdaAny -> AgdaAny
d_refl_90 v0 = coe d_refl_34 (coe d_isEquivalence_80 (coe v0))
-- Relation.Binary.Structures.IsPreorder.Eq.reflexive
d_reflexive_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_70 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_92 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_92 v6
du_reflexive_92 ::
  T_IsPreorder_70 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_92 v0 v1 v2 v3
  = coe du_reflexive_40 (coe d_isEquivalence_80 (coe v0)) v1
-- Relation.Binary.Structures.IsPreorder.Eq.sym
d_sym_94 ::
  T_IsPreorder_70 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_94 v0 = coe d_sym_36 (coe d_isEquivalence_80 (coe v0))
-- Relation.Binary.Structures.IsPreorder.Eq.trans
d_trans_96 ::
  T_IsPreorder_70 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_96 v0 = coe d_trans_38 (coe d_isEquivalence_80 (coe v0))
-- Relation.Binary.Structures.IsPreorder.refl
d_refl_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> T_IsPreorder_70 -> AgdaAny -> AgdaAny
d_refl_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_refl_98 v6 v7
du_refl_98 :: T_IsPreorder_70 -> AgdaAny -> AgdaAny
du_refl_98 v0 v1
  = coe
      d_reflexive_82 v0 v1 v1
      (coe d_refl_34 (d_isEquivalence_80 (coe v0)) v1)
-- Relation.Binary.Structures.IsPreorder.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_70 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                    v8 v9 v10 v11
  = du_'8818''45'resp'737''45''8776'_100 v6 v7 v8 v9 v10 v11
du_'8818''45'resp'737''45''8776'_100 ::
  T_IsPreorder_70 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_100 v0 v1 v2 v3 v4 v5
  = coe
      d_trans_84 v0 v3 v2 v1
      (coe
         d_reflexive_82 v0 v3 v2
         (coe d_sym_36 (d_isEquivalence_80 (coe v0)) v2 v3 v4))
      v5
-- Relation.Binary.Structures.IsPreorder.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_70 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                    v8 v9 v10 v11
  = du_'8818''45'resp'691''45''8776'_106 v6 v7 v8 v9 v10 v11
du_'8818''45'resp'691''45''8776'_106 ::
  T_IsPreorder_70 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_106 v0 v1 v2 v3 v4 v5
  = coe d_trans_84 v0 v1 v2 v3 v5 (coe d_reflexive_82 v0 v2 v3 v4)
-- Relation.Binary.Structures.IsPreorder.≲-resp-≈
d_'8818''45'resp'45''8776'_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_70 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_112 v6
du_'8818''45'resp'45''8776'_112 ::
  T_IsPreorder_70 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_112 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8818''45'resp'691''45''8776'_106 (coe v0))
      (coe du_'8818''45'resp'737''45''8776'_100 (coe v0))
-- Relation.Binary.Structures.IsPreorder.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_70 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_114 v6
du_'8764''45'resp'737''45''8776'_114 ::
  T_IsPreorder_70 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_114 v0
  = coe du_'8818''45'resp'737''45''8776'_100 (coe v0)
-- Relation.Binary.Structures.IsPreorder.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_70 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_116 v6
du_'8764''45'resp'691''45''8776'_116 ::
  T_IsPreorder_70 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_116 v0
  = coe du_'8818''45'resp'691''45''8776'_106 (coe v0)
-- Relation.Binary.Structures.IsPreorder.∼-resp-≈
d_'8764''45'resp'45''8776'_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPreorder_70 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_118 v6
du_'8764''45'resp'45''8776'_118 ::
  T_IsPreorder_70 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_118 v0
  = coe du_'8818''45'resp'45''8776'_112 (coe v0)
-- Relation.Binary.Structures.IsTotalPreorder
d_IsTotalPreorder_124 a0 a1 a2 a3 a4 a5 = ()
data T_IsTotalPreorder_124
  = C_IsTotalPreorder'46'constructor_8325 T_IsPreorder_70
                                          (AgdaAny ->
                                           AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Relation.Binary.Structures.IsTotalPreorder.isPreorder
d_isPreorder_132 :: T_IsTotalPreorder_124 -> T_IsPreorder_70
d_isPreorder_132 v0
  = case coe v0 of
      C_IsTotalPreorder'46'constructor_8325 v1 v2 -> coe v1
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsTotalPreorder.total
d_total_134 ::
  T_IsTotalPreorder_124 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_134 v0
  = case coe v0 of
      C_IsTotalPreorder'46'constructor_8325 v1 v2 -> coe v2
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsTotalPreorder._.isEquivalence
d_isEquivalence_138 :: T_IsTotalPreorder_124 -> T_IsEquivalence_26
d_isEquivalence_138 v0
  = coe d_isEquivalence_80 (coe d_isPreorder_132 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.refl
d_refl_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_124 -> AgdaAny -> AgdaAny
d_refl_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_140 v6
du_refl_140 :: T_IsTotalPreorder_124 -> AgdaAny -> AgdaAny
du_refl_140 v0 = coe du_refl_98 (coe d_isPreorder_132 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.reflexive
d_reflexive_142 ::
  T_IsTotalPreorder_124 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_142 v0
  = coe d_reflexive_82 (coe d_isPreorder_132 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.trans
d_trans_144 ::
  T_IsTotalPreorder_124 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_144 v0 = coe d_trans_84 (coe d_isPreorder_132 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.∼-resp-≈
d_'8764''45'resp'45''8776'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_124 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_146 v6
du_'8764''45'resp'45''8776'_146 ::
  T_IsTotalPreorder_124 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_146 v0
  = coe
      du_'8764''45'resp'45''8776'_118 (coe d_isPreorder_132 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_124 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_148 v6
du_'8764''45'resp'691''45''8776'_148 ::
  T_IsTotalPreorder_124 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_148 v0
  = coe
      du_'8764''45'resp'691''45''8776'_116
      (coe d_isPreorder_132 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_124 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_150 v6
du_'8764''45'resp'737''45''8776'_150 ::
  T_IsTotalPreorder_124 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_150 v0
  = coe
      du_'8764''45'resp'737''45''8776'_114
      (coe d_isPreorder_132 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.≲-resp-≈
d_'8818''45'resp'45''8776'_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_124 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_152 v6
du_'8818''45'resp'45''8776'_152 ::
  T_IsTotalPreorder_124 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_152 v0
  = coe
      du_'8818''45'resp'45''8776'_112 (coe d_isPreorder_132 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_124 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'691''45''8776'_154 v6
du_'8818''45'resp'691''45''8776'_154 ::
  T_IsTotalPreorder_124 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_154 v0
  = coe
      du_'8818''45'resp'691''45''8776'_106
      (coe d_isPreorder_132 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_124 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'737''45''8776'_156 v6
du_'8818''45'resp'737''45''8776'_156 ::
  T_IsTotalPreorder_124 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_156 v0
  = coe
      du_'8818''45'resp'737''45''8776'_100
      (coe d_isPreorder_132 (coe v0))
-- Relation.Binary.Structures.IsTotalPreorder._.Eq.isPartialEquivalence
d_isPartialEquivalence_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_124 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_160 v6
du_isPartialEquivalence_160 ::
  T_IsTotalPreorder_124 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_160 v0
  = let v1 = d_isPreorder_132 (coe v0) in
    coe
      (coe du_isPartialEquivalence_42 (coe d_isEquivalence_80 (coe v1)))
-- Relation.Binary.Structures.IsTotalPreorder._.Eq.refl
d_refl_162 :: T_IsTotalPreorder_124 -> AgdaAny -> AgdaAny
d_refl_162 v0
  = coe
      d_refl_34 (coe d_isEquivalence_80 (coe d_isPreorder_132 (coe v0)))
-- Relation.Binary.Structures.IsTotalPreorder._.Eq.reflexive
d_reflexive_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalPreorder_124 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_164 v6
du_reflexive_164 ::
  T_IsTotalPreorder_124 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_164 v0
  = let v1 = d_isPreorder_132 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_40 (coe d_isEquivalence_80 (coe v1)) v2)
-- Relation.Binary.Structures.IsTotalPreorder._.Eq.sym
d_sym_166 ::
  T_IsTotalPreorder_124 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_166 v0
  = coe
      d_sym_36 (coe d_isEquivalence_80 (coe d_isPreorder_132 (coe v0)))
-- Relation.Binary.Structures.IsTotalPreorder._.Eq.trans
d_trans_168 ::
  T_IsTotalPreorder_124 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_168 v0
  = coe
      d_trans_38 (coe d_isEquivalence_80 (coe d_isPreorder_132 (coe v0)))
-- Relation.Binary.Structures.IsPartialOrder
d_IsPartialOrder_174 a0 a1 a2 a3 a4 a5 = ()
data T_IsPartialOrder_174
  = C_IsPartialOrder'46'constructor_9853 T_IsPreorder_70
                                         (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Structures.IsPartialOrder.isPreorder
d_isPreorder_182 :: T_IsPartialOrder_174 -> T_IsPreorder_70
d_isPreorder_182 v0
  = case coe v0 of
      C_IsPartialOrder'46'constructor_9853 v1 v2 -> coe v1
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPartialOrder.antisym
d_antisym_184 ::
  T_IsPartialOrder_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_184 v0
  = case coe v0 of
      C_IsPartialOrder'46'constructor_9853 v1 v2 -> coe v2
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsPartialOrder._.isEquivalence
d_isEquivalence_188 :: T_IsPartialOrder_174 -> T_IsEquivalence_26
d_isEquivalence_188 v0
  = coe d_isEquivalence_80 (coe d_isPreorder_182 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.refl
d_refl_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_174 -> AgdaAny -> AgdaAny
d_refl_190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_190 v6
du_refl_190 :: T_IsPartialOrder_174 -> AgdaAny -> AgdaAny
du_refl_190 v0 = coe du_refl_98 (coe d_isPreorder_182 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.reflexive
d_reflexive_192 ::
  T_IsPartialOrder_174 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_192 v0
  = coe d_reflexive_82 (coe d_isPreorder_182 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.trans
d_trans_194 ::
  T_IsPartialOrder_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_194 v0 = coe d_trans_84 (coe d_isPreorder_182 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_174 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_196 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_196 v6
du_'8764''45'resp'45''8776'_196 ::
  T_IsPartialOrder_174 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_196 v0
  = coe
      du_'8764''45'resp'45''8776'_118 (coe d_isPreorder_182 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_198 v6
du_'8764''45'resp'691''45''8776'_198 ::
  T_IsPartialOrder_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_198 v0
  = coe
      du_'8764''45'resp'691''45''8776'_116
      (coe d_isPreorder_182 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_200 v6
du_'8764''45'resp'737''45''8776'_200 ::
  T_IsPartialOrder_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_200 v0
  = coe
      du_'8764''45'resp'737''45''8776'_114
      (coe d_isPreorder_182 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_174 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_202 v6
du_'8818''45'resp'45''8776'_202 ::
  T_IsPartialOrder_174 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_202 v0
  = coe
      du_'8818''45'resp'45''8776'_112 (coe d_isPreorder_182 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'691''45''8776'_204 v6
du_'8818''45'resp'691''45''8776'_204 ::
  T_IsPartialOrder_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_204 v0
  = coe
      du_'8818''45'resp'691''45''8776'_106
      (coe d_isPreorder_182 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'737''45''8776'_206 v6
du_'8818''45'resp'737''45''8776'_206 ::
  T_IsPartialOrder_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_206 v0
  = coe
      du_'8818''45'resp'737''45''8776'_100
      (coe d_isPreorder_182 (coe v0))
-- Relation.Binary.Structures.IsPartialOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_174 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_210 v6
du_isPartialEquivalence_210 ::
  T_IsPartialOrder_174 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_210 v0
  = let v1 = d_isPreorder_182 (coe v0) in
    coe
      (coe du_isPartialEquivalence_42 (coe d_isEquivalence_80 (coe v1)))
-- Relation.Binary.Structures.IsPartialOrder._.Eq.refl
d_refl_212 :: T_IsPartialOrder_174 -> AgdaAny -> AgdaAny
d_refl_212 v0
  = coe
      d_refl_34 (coe d_isEquivalence_80 (coe d_isPreorder_182 (coe v0)))
-- Relation.Binary.Structures.IsPartialOrder._.Eq.reflexive
d_reflexive_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsPartialOrder_174 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_214 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_214 v6
du_reflexive_214 ::
  T_IsPartialOrder_174 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_214 v0
  = let v1 = d_isPreorder_182 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_40 (coe d_isEquivalence_80 (coe v1)) v2)
-- Relation.Binary.Structures.IsPartialOrder._.Eq.sym
d_sym_216 ::
  T_IsPartialOrder_174 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_216 v0
  = coe
      d_sym_36 (coe d_isEquivalence_80 (coe d_isPreorder_182 (coe v0)))
-- Relation.Binary.Structures.IsPartialOrder._.Eq.trans
d_trans_218 ::
  T_IsPartialOrder_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_218 v0
  = coe
      d_trans_38 (coe d_isEquivalence_80 (coe d_isPreorder_182 (coe v0)))
-- Relation.Binary.Structures.IsDecPartialOrder
d_IsDecPartialOrder_224 a0 a1 a2 a3 a4 a5 = ()
data T_IsDecPartialOrder_224
  = C_IsDecPartialOrder'46'constructor_11683 T_IsPartialOrder_174
                                             (AgdaAny ->
                                              AgdaAny ->
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                                             (AgdaAny ->
                                              AgdaAny ->
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
-- Relation.Binary.Structures.IsDecPartialOrder.isPartialOrder
d_isPartialOrder_234 ::
  T_IsDecPartialOrder_224 -> T_IsPartialOrder_174
d_isPartialOrder_234 v0
  = case coe v0 of
      C_IsDecPartialOrder'46'constructor_11683 v1 v2 v3 -> coe v1
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecPartialOrder._≟_
d__'8799'__236 ::
  T_IsDecPartialOrder_224 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__236 v0
  = case coe v0 of
      C_IsDecPartialOrder'46'constructor_11683 v1 v2 v3 -> coe v2
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecPartialOrder._≤?_
d__'8804''63'__238 ::
  T_IsDecPartialOrder_224 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__238 v0
  = case coe v0 of
      C_IsDecPartialOrder'46'constructor_11683 v1 v2 v3 -> coe v3
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecPartialOrder._.antisym
d_antisym_242 ::
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_242 v0
  = coe d_antisym_184 (coe d_isPartialOrder_234 (coe v0))
-- Relation.Binary.Structures.IsDecPartialOrder._.isEquivalence
d_isEquivalence_244 ::
  T_IsDecPartialOrder_224 -> T_IsEquivalence_26
d_isEquivalence_244 v0
  = coe
      d_isEquivalence_80
      (coe d_isPreorder_182 (coe d_isPartialOrder_234 (coe v0)))
-- Relation.Binary.Structures.IsDecPartialOrder._.isPreorder
d_isPreorder_246 :: T_IsDecPartialOrder_224 -> T_IsPreorder_70
d_isPreorder_246 v0
  = coe d_isPreorder_182 (coe d_isPartialOrder_234 (coe v0))
-- Relation.Binary.Structures.IsDecPartialOrder._.refl
d_refl_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 -> AgdaAny -> AgdaAny
d_refl_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_248 v6
du_refl_248 :: T_IsDecPartialOrder_224 -> AgdaAny -> AgdaAny
du_refl_248 v0
  = let v1 = d_isPartialOrder_234 (coe v0) in
    coe (coe du_refl_98 (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.reflexive
d_reflexive_250 ::
  T_IsDecPartialOrder_224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_250 v0
  = coe
      d_reflexive_82
      (coe d_isPreorder_182 (coe d_isPartialOrder_234 (coe v0)))
-- Relation.Binary.Structures.IsDecPartialOrder._.trans
d_trans_252 ::
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_252 v0
  = coe
      d_trans_84
      (coe d_isPreorder_182 (coe d_isPartialOrder_234 (coe v0)))
-- Relation.Binary.Structures.IsDecPartialOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_254 v6
du_'8764''45'resp'45''8776'_254 ::
  T_IsDecPartialOrder_224 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_254 v0
  = let v1 = d_isPartialOrder_234 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'45''8776'_118 (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_256 v6
du_'8764''45'resp'691''45''8776'_256 ::
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_256 v0
  = let v1 = d_isPartialOrder_234 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'691''45''8776'_116
         (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_258 v6
du_'8764''45'resp'737''45''8776'_258 ::
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_258 v0
  = let v1 = d_isPartialOrder_234 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'737''45''8776'_114
         (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_260 v6
du_'8818''45'resp'45''8776'_260 ::
  T_IsDecPartialOrder_224 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_260 v0
  = let v1 = d_isPartialOrder_234 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'45''8776'_112 (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'691''45''8776'_262 v6
du_'8818''45'resp'691''45''8776'_262 ::
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_262 v0
  = let v1 = d_isPartialOrder_234 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'691''45''8776'_106
         (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'737''45''8776'_264 v6
du_'8818''45'resp'737''45''8776'_264 ::
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_264 v0
  = let v1 = d_isPartialOrder_234 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'737''45''8776'_100
         (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder.Eq.isDecEquivalence
d_isDecEquivalence_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 -> T_IsDecEquivalence_44
d_isDecEquivalence_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_268 v6
du_isDecEquivalence_268 ::
  T_IsDecPartialOrder_224 -> T_IsDecEquivalence_44
du_isDecEquivalence_268 v0
  = coe
      C_IsDecEquivalence'46'constructor_3083
      (coe
         d_isEquivalence_80
         (coe d_isPreorder_182 (coe d_isPartialOrder_234 (coe v0))))
      (coe d__'8799'__236 (coe v0))
-- Relation.Binary.Structures.IsDecPartialOrder.Eq._._≟_
d__'8799'__272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__272 v6
du__'8799'__272 ::
  T_IsDecPartialOrder_224 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__272 v0 = coe d__'8799'__236 (coe v0)
-- Relation.Binary.Structures.IsDecPartialOrder.Eq._.isEquivalence
d_isEquivalence_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 -> T_IsEquivalence_26
d_isEquivalence_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_274 v6
du_isEquivalence_274 ::
  T_IsDecPartialOrder_224 -> T_IsEquivalence_26
du_isEquivalence_274 v0
  = coe
      d_isEquivalence_80
      (coe d_isPreorder_182 (coe d_isPartialOrder_234 (coe v0)))
-- Relation.Binary.Structures.IsDecPartialOrder.Eq._.isPartialEquivalence
d_isPartialEquivalence_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_276 v6
du_isPartialEquivalence_276 ::
  T_IsDecPartialOrder_224 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_276 v0
  = let v1 = coe du_isDecEquivalence_268 (coe v0) in
    coe
      (coe du_isPartialEquivalence_42 (coe d_isEquivalence_50 (coe v1)))
-- Relation.Binary.Structures.IsDecPartialOrder.Eq._.refl
d_refl_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 -> AgdaAny -> AgdaAny
d_refl_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_278 v6
du_refl_278 :: T_IsDecPartialOrder_224 -> AgdaAny -> AgdaAny
du_refl_278 v0
  = coe
      d_refl_34
      (coe
         d_isEquivalence_80
         (coe d_isPreorder_182 (coe d_isPartialOrder_234 (coe v0))))
-- Relation.Binary.Structures.IsDecPartialOrder.Eq._.reflexive
d_reflexive_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_280 v6
du_reflexive_280 ::
  T_IsDecPartialOrder_224 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_280 v0
  = let v1 = coe du_isDecEquivalence_268 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_40 (coe d_isEquivalence_50 (coe v1)) v2)
-- Relation.Binary.Structures.IsDecPartialOrder.Eq._.sym
d_sym_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_282 v6
du_sym_282 ::
  T_IsDecPartialOrder_224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_282 v0
  = coe
      d_sym_36
      (coe
         d_isEquivalence_80
         (coe d_isPreorder_182 (coe d_isPartialOrder_234 (coe v0))))
-- Relation.Binary.Structures.IsDecPartialOrder.Eq._.trans
d_trans_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_284 v6
du_trans_284 ::
  T_IsDecPartialOrder_224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_284 v0
  = coe
      d_trans_38
      (coe
         d_isEquivalence_80
         (coe d_isPreorder_182 (coe d_isPartialOrder_234 (coe v0))))
-- Relation.Binary.Structures.IsStrictPartialOrder
d_IsStrictPartialOrder_290 a0 a1 a2 a3 a4 a5 = ()
data T_IsStrictPartialOrder_290
  = C_IsStrictPartialOrder'46'constructor_14045 T_IsEquivalence_26
                                                (AgdaAny ->
                                                 AgdaAny ->
                                                 AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                                MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Relation.Binary.Structures.IsStrictPartialOrder.isEquivalence
d_isEquivalence_302 ::
  T_IsStrictPartialOrder_290 -> T_IsEquivalence_26
d_isEquivalence_302 v0
  = case coe v0 of
      C_IsStrictPartialOrder'46'constructor_14045 v1 v3 v4 -> coe v1
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsStrictPartialOrder.irrefl
d_irrefl_304 ::
  T_IsStrictPartialOrder_290 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_304 = erased
-- Relation.Binary.Structures.IsStrictPartialOrder.trans
d_trans_306 ::
  T_IsStrictPartialOrder_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_306 v0
  = case coe v0 of
      C_IsStrictPartialOrder'46'constructor_14045 v1 v3 v4 -> coe v3
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsStrictPartialOrder.<-resp-≈
d_'60''45'resp'45''8776'_308 ::
  T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_308 v0
  = case coe v0 of
      C_IsStrictPartialOrder'46'constructor_14045 v1 v3 v4 -> coe v4
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsStrictPartialOrder.Eq.isPartialEquivalence
d_isPartialEquivalence_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictPartialOrder_290 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_312 v6
du_isPartialEquivalence_312 ::
  T_IsStrictPartialOrder_290 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_312 v0
  = coe du_isPartialEquivalence_42 (coe d_isEquivalence_302 (coe v0))
-- Relation.Binary.Structures.IsStrictPartialOrder.Eq.refl
d_refl_314 :: T_IsStrictPartialOrder_290 -> AgdaAny -> AgdaAny
d_refl_314 v0 = coe d_refl_34 (coe d_isEquivalence_302 (coe v0))
-- Relation.Binary.Structures.IsStrictPartialOrder.Eq.reflexive
d_reflexive_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictPartialOrder_290 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_316 v6
du_reflexive_316 ::
  T_IsStrictPartialOrder_290 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_316 v0 v1 v2 v3
  = coe du_reflexive_40 (coe d_isEquivalence_302 (coe v0)) v1
-- Relation.Binary.Structures.IsStrictPartialOrder.Eq.sym
d_sym_318 ::
  T_IsStrictPartialOrder_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_318 v0 = coe d_sym_36 (coe d_isEquivalence_302 (coe v0))
-- Relation.Binary.Structures.IsStrictPartialOrder.Eq.trans
d_trans_320 ::
  T_IsStrictPartialOrder_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_320 v0 = coe d_trans_38 (coe d_isEquivalence_302 (coe v0))
-- Relation.Binary.Structures.IsStrictPartialOrder.asym
d_asym_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictPartialOrder_290 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_322 = erased
-- Relation.Binary.Structures.IsStrictPartialOrder.<-respʳ-≈
d_'60''45'resp'691''45''8776'_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictPartialOrder_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
                                  v9
  = du_'60''45'resp'691''45''8776'_328 v6 v7 v8 v9
du_'60''45'resp'691''45''8776'_328 ::
  T_IsStrictPartialOrder_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_328 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (d_'60''45'resp'45''8776'_308 (coe v0)) v1 v2 v3
-- Relation.Binary.Structures.IsStrictPartialOrder.<-respˡ-≈
d_'60''45'resp'737''45''8776'_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictPartialOrder_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
                                  v9
  = du_'60''45'resp'737''45''8776'_330 v6 v7 v8 v9
du_'60''45'resp'737''45''8776'_330 ::
  T_IsStrictPartialOrder_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_330 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (d_'60''45'resp'45''8776'_308 (coe v0)) v1 v2 v3
-- Relation.Binary.Structures.IsDecStrictPartialOrder
d_IsDecStrictPartialOrder_336 a0 a1 a2 a3 a4 a5 = ()
data T_IsDecStrictPartialOrder_336
  = C_IsDecStrictPartialOrder'46'constructor_18663 T_IsStrictPartialOrder_290
                                                   (AgdaAny ->
                                                    AgdaAny ->
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                                                   (AgdaAny ->
                                                    AgdaAny ->
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
-- Relation.Binary.Structures.IsDecStrictPartialOrder.isStrictPartialOrder
d_isStrictPartialOrder_346 ::
  T_IsDecStrictPartialOrder_336 -> T_IsStrictPartialOrder_290
d_isStrictPartialOrder_346 v0
  = case coe v0 of
      C_IsDecStrictPartialOrder'46'constructor_18663 v1 v2 v3 -> coe v1
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecStrictPartialOrder._≟_
d__'8799'__348 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__348 v0
  = case coe v0 of
      C_IsDecStrictPartialOrder'46'constructor_18663 v1 v2 v3 -> coe v2
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecStrictPartialOrder._<?_
d__'60''63'__350 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__350 v0
  = case coe v0 of
      C_IsDecStrictPartialOrder'46'constructor_18663 v1 v2 v3 -> coe v3
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.<-resp-≈
d_'60''45'resp'45''8776'_354 ::
  T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_354 v0
  = coe
      d_'60''45'resp'45''8776'_308
      (coe d_isStrictPartialOrder_346 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.<-respʳ-≈
d_'60''45'resp'691''45''8776'_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'691''45''8776'_356 v6
du_'60''45'resp'691''45''8776'_356 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_356 v0
  = coe
      du_'60''45'resp'691''45''8776'_328
      (coe d_isStrictPartialOrder_346 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.<-respˡ-≈
d_'60''45'resp'737''45''8776'_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'737''45''8776'_358 v6
du_'60''45'resp'737''45''8776'_358 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_358 v0
  = coe
      du_'60''45'resp'737''45''8776'_330
      (coe d_isStrictPartialOrder_346 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.asym
d_asym_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_360 = erased
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.irrefl
d_irrefl_362 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_362 = erased
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.isEquivalence
d_isEquivalence_364 ::
  T_IsDecStrictPartialOrder_336 -> T_IsEquivalence_26
d_isEquivalence_364 v0
  = coe d_isEquivalence_302 (coe d_isStrictPartialOrder_346 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.trans
d_trans_366 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_366 v0
  = coe d_trans_306 (coe d_isStrictPartialOrder_346 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.Eq.isPartialEquivalence
d_isPartialEquivalence_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_370 v6
du_isPartialEquivalence_370 ::
  T_IsDecStrictPartialOrder_336 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_370 v0
  = let v1 = d_isStrictPartialOrder_346 (coe v0) in
    coe
      (coe du_isPartialEquivalence_42 (coe d_isEquivalence_302 (coe v1)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.Eq.refl
d_refl_372 :: T_IsDecStrictPartialOrder_336 -> AgdaAny -> AgdaAny
d_refl_372 v0
  = coe
      d_refl_34
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_346 (coe v0)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.Eq.reflexive
d_reflexive_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_374 v6
du_reflexive_374 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_374 v0
  = let v1 = d_isStrictPartialOrder_346 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_40 (coe d_isEquivalence_302 (coe v1)) v2)
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.Eq.sym
d_sym_376 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_376 v0
  = coe
      d_sym_36
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_346 (coe v0)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.SPO.Eq.trans
d_trans_378 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_378 v0
  = coe
      d_trans_38
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_346 (coe v0)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq.isDecEquivalence
d_isDecEquivalence_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 -> T_IsDecEquivalence_44
d_isDecEquivalence_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_382 v6
du_isDecEquivalence_382 ::
  T_IsDecStrictPartialOrder_336 -> T_IsDecEquivalence_44
du_isDecEquivalence_382 v0
  = coe
      C_IsDecEquivalence'46'constructor_3083
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_346 (coe v0)))
      (coe d__'8799'__348 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._._≟_
d__'8799'__386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__386 v6
du__'8799'__386 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__386 v0 = coe d__'8799'__348 (coe v0)
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.isEquivalence
d_isEquivalence_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 -> T_IsEquivalence_26
d_isEquivalence_388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_388 v6
du_isEquivalence_388 ::
  T_IsDecStrictPartialOrder_336 -> T_IsEquivalence_26
du_isEquivalence_388 v0
  = coe d_isEquivalence_302 (coe d_isStrictPartialOrder_346 (coe v0))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.isPartialEquivalence
d_isPartialEquivalence_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_390 v6
du_isPartialEquivalence_390 ::
  T_IsDecStrictPartialOrder_336 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_390 v0
  = let v1 = coe du_isDecEquivalence_382 (coe v0) in
    coe
      (coe du_isPartialEquivalence_42 (coe d_isEquivalence_50 (coe v1)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.refl
d_refl_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 -> AgdaAny -> AgdaAny
d_refl_392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_392 v6
du_refl_392 :: T_IsDecStrictPartialOrder_336 -> AgdaAny -> AgdaAny
du_refl_392 v0
  = coe
      d_refl_34
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_346 (coe v0)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.reflexive
d_reflexive_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_394 v6
du_reflexive_394 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_394 v0
  = let v1 = coe du_isDecEquivalence_382 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_40 (coe d_isEquivalence_50 (coe v1)) v2)
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.sym
d_sym_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_396 v6
du_sym_396 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_396 v0
  = coe
      d_sym_36
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_346 (coe v0)))
-- Relation.Binary.Structures.IsDecStrictPartialOrder.Eq._.trans
d_trans_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_398 v6
du_trans_398 ::
  T_IsDecStrictPartialOrder_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_398 v0
  = coe
      d_trans_38
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_346 (coe v0)))
-- Relation.Binary.Structures.IsTotalOrder
d_IsTotalOrder_404 a0 a1 a2 a3 a4 a5 = ()
data T_IsTotalOrder_404
  = C_IsTotalOrder'46'constructor_20555 T_IsPartialOrder_174
                                        (AgdaAny ->
                                         AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Relation.Binary.Structures.IsTotalOrder.isPartialOrder
d_isPartialOrder_412 :: T_IsTotalOrder_404 -> T_IsPartialOrder_174
d_isPartialOrder_412 v0
  = case coe v0 of
      C_IsTotalOrder'46'constructor_20555 v1 v2 -> coe v1
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsTotalOrder.total
d_total_414 ::
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_414 v0
  = case coe v0 of
      C_IsTotalOrder'46'constructor_20555 v1 v2 -> coe v2
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsTotalOrder._.antisym
d_antisym_418 ::
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_418 v0
  = coe d_antisym_184 (coe d_isPartialOrder_412 (coe v0))
-- Relation.Binary.Structures.IsTotalOrder._.isEquivalence
d_isEquivalence_420 :: T_IsTotalOrder_404 -> T_IsEquivalence_26
d_isEquivalence_420 v0
  = coe
      d_isEquivalence_80
      (coe d_isPreorder_182 (coe d_isPartialOrder_412 (coe v0)))
-- Relation.Binary.Structures.IsTotalOrder._.isPreorder
d_isPreorder_422 :: T_IsTotalOrder_404 -> T_IsPreorder_70
d_isPreorder_422 v0
  = coe d_isPreorder_182 (coe d_isPartialOrder_412 (coe v0))
-- Relation.Binary.Structures.IsTotalOrder._.refl
d_refl_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_404 -> AgdaAny -> AgdaAny
d_refl_424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_424 v6
du_refl_424 :: T_IsTotalOrder_404 -> AgdaAny -> AgdaAny
du_refl_424 v0
  = let v1 = d_isPartialOrder_412 (coe v0) in
    coe (coe du_refl_98 (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.reflexive
d_reflexive_426 ::
  T_IsTotalOrder_404 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_426 v0
  = coe
      d_reflexive_82
      (coe d_isPreorder_182 (coe d_isPartialOrder_412 (coe v0)))
-- Relation.Binary.Structures.IsTotalOrder._.trans
d_trans_428 ::
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_428 v0
  = coe
      d_trans_84
      (coe d_isPreorder_182 (coe d_isPartialOrder_412 (coe v0)))
-- Relation.Binary.Structures.IsTotalOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_404 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_430 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_430 v6
du_'8764''45'resp'45''8776'_430 ::
  T_IsTotalOrder_404 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_430 v0
  = let v1 = d_isPartialOrder_412 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'45''8776'_118 (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_432 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_432 v6
du_'8764''45'resp'691''45''8776'_432 ::
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_432 v0
  = let v1 = d_isPartialOrder_412 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'691''45''8776'_116
         (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_434 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_434 v6
du_'8764''45'resp'737''45''8776'_434 ::
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_434 v0
  = let v1 = d_isPartialOrder_412 (coe v0) in
    coe
      (coe
         du_'8764''45'resp'737''45''8776'_114
         (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_404 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_436 v6
du_'8818''45'resp'45''8776'_436 ::
  T_IsTotalOrder_404 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_436 v0
  = let v1 = d_isPartialOrder_412 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'45''8776'_112 (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'691''45''8776'_438 v6
du_'8818''45'resp'691''45''8776'_438 ::
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_438 v0
  = let v1 = d_isPartialOrder_412 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'691''45''8776'_106
         (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'737''45''8776'_440 v6
du_'8818''45'resp'737''45''8776'_440 ::
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_440 v0
  = let v1 = d_isPartialOrder_412 (coe v0) in
    coe
      (coe
         du_'8818''45'resp'737''45''8776'_100
         (coe d_isPreorder_182 (coe v1)))
-- Relation.Binary.Structures.IsTotalOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_404 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_444 v6
du_isPartialEquivalence_444 ::
  T_IsTotalOrder_404 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_444 v0
  = let v1 = d_isPartialOrder_412 (coe v0) in
    coe
      (let v2 = d_isPreorder_182 (coe v1) in
       coe
         (coe du_isPartialEquivalence_42 (coe d_isEquivalence_80 (coe v2))))
-- Relation.Binary.Structures.IsTotalOrder._.Eq.refl
d_refl_446 :: T_IsTotalOrder_404 -> AgdaAny -> AgdaAny
d_refl_446 v0
  = coe
      d_refl_34
      (coe
         d_isEquivalence_80
         (coe d_isPreorder_182 (coe d_isPartialOrder_412 (coe v0))))
-- Relation.Binary.Structures.IsTotalOrder._.Eq.reflexive
d_reflexive_448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_404 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_448 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_448 v6
du_reflexive_448 ::
  T_IsTotalOrder_404 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_448 v0
  = let v1 = d_isPartialOrder_412 (coe v0) in
    coe
      (let v2 = d_isPreorder_182 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe du_reflexive_40 (coe d_isEquivalence_80 (coe v2)) v3))
-- Relation.Binary.Structures.IsTotalOrder._.Eq.sym
d_sym_450 ::
  T_IsTotalOrder_404 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_450 v0
  = coe
      d_sym_36
      (coe
         d_isEquivalence_80
         (coe d_isPreorder_182 (coe d_isPartialOrder_412 (coe v0))))
-- Relation.Binary.Structures.IsTotalOrder._.Eq.trans
d_trans_452 ::
  T_IsTotalOrder_404 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_452 v0
  = coe
      d_trans_38
      (coe
         d_isEquivalence_80
         (coe d_isPreorder_182 (coe d_isPartialOrder_412 (coe v0))))
-- Relation.Binary.Structures.IsTotalOrder.isTotalPreorder
d_isTotalPreorder_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsTotalOrder_404 -> T_IsTotalPreorder_124
d_isTotalPreorder_454 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isTotalPreorder_454 v6
du_isTotalPreorder_454 ::
  T_IsTotalOrder_404 -> T_IsTotalPreorder_124
du_isTotalPreorder_454 v0
  = coe
      C_IsTotalPreorder'46'constructor_8325
      (coe d_isPreorder_182 (coe d_isPartialOrder_412 (coe v0)))
      (coe d_total_414 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder
d_IsDecTotalOrder_460 a0 a1 a2 a3 a4 a5 = ()
data T_IsDecTotalOrder_460
  = C_IsDecTotalOrder'46'constructor_22695 T_IsTotalOrder_404
                                           (AgdaAny ->
                                            AgdaAny ->
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
                                           (AgdaAny ->
                                            AgdaAny ->
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
-- Relation.Binary.Structures.IsDecTotalOrder.isTotalOrder
d_isTotalOrder_470 :: T_IsDecTotalOrder_460 -> T_IsTotalOrder_404
d_isTotalOrder_470 v0
  = case coe v0 of
      C_IsDecTotalOrder'46'constructor_22695 v1 v2 v3 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecTotalOrder._≟_
d__'8799'__472 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__472 v0
  = case coe v0 of
      C_IsDecTotalOrder'46'constructor_22695 v1 v2 v3 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecTotalOrder._≤?_
d__'8804''63'__474 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__474 v0
  = case coe v0 of
      C_IsDecTotalOrder'46'constructor_22695 v1 v2 v3 -> coe v3
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDecTotalOrder._.antisym
d_antisym_478 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_478 v0
  = coe
      d_antisym_184
      (coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0)))
-- Relation.Binary.Structures.IsDecTotalOrder._.isEquivalence
d_isEquivalence_480 :: T_IsDecTotalOrder_460 -> T_IsEquivalence_26
d_isEquivalence_480 v0
  = coe
      d_isEquivalence_80
      (coe
         d_isPreorder_182
         (coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0))))
-- Relation.Binary.Structures.IsDecTotalOrder._.isPartialOrder
d_isPartialOrder_482 ::
  T_IsDecTotalOrder_460 -> T_IsPartialOrder_174
d_isPartialOrder_482 v0
  = coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder._.isPreorder
d_isPreorder_484 :: T_IsDecTotalOrder_460 -> T_IsPreorder_70
d_isPreorder_484 v0
  = coe
      d_isPreorder_182
      (coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0)))
-- Relation.Binary.Structures.IsDecTotalOrder._.isTotalPreorder
d_isTotalPreorder_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 -> T_IsTotalPreorder_124
d_isTotalPreorder_486 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isTotalPreorder_486 v6
du_isTotalPreorder_486 ::
  T_IsDecTotalOrder_460 -> T_IsTotalPreorder_124
du_isTotalPreorder_486 v0
  = coe du_isTotalPreorder_454 (coe d_isTotalOrder_470 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder._.refl
d_refl_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 -> AgdaAny -> AgdaAny
d_refl_488 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_488 v6
du_refl_488 :: T_IsDecTotalOrder_460 -> AgdaAny -> AgdaAny
du_refl_488 v0
  = let v1 = d_isTotalOrder_470 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_412 (coe v1) in
       coe (coe du_refl_98 (coe d_isPreorder_182 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.reflexive
d_reflexive_490 ::
  T_IsDecTotalOrder_460 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_490 v0
  = coe
      d_reflexive_82
      (coe
         d_isPreorder_182
         (coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0))))
-- Relation.Binary.Structures.IsDecTotalOrder._.total
d_total_492 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_492 v0 = coe d_total_414 (coe d_isTotalOrder_470 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder._.trans
d_trans_494 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_494 v0
  = coe
      d_trans_84
      (coe
         d_isPreorder_182
         (coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0))))
-- Relation.Binary.Structures.IsDecTotalOrder._.∼-resp-≈
d_'8764''45'resp'45''8776'_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'45''8776'_496 v6
du_'8764''45'resp'45''8776'_496 ::
  T_IsDecTotalOrder_460 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_496 v0
  = let v1 = d_isTotalOrder_470 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_412 (coe v1) in
       coe
         (coe
            du_'8764''45'resp'45''8776'_118 (coe d_isPreorder_182 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_498 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'691''45''8776'_498 v6
du_'8764''45'resp'691''45''8776'_498 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_498 v0
  = let v1 = d_isTotalOrder_470 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_412 (coe v1) in
       coe
         (coe
            du_'8764''45'resp'691''45''8776'_116
            (coe d_isPreorder_182 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_500 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8764''45'resp'737''45''8776'_500 v6
du_'8764''45'resp'737''45''8776'_500 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_500 v0
  = let v1 = d_isTotalOrder_470 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_412 (coe v1) in
       coe
         (coe
            du_'8764''45'resp'737''45''8776'_114
            (coe d_isPreorder_182 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.≲-resp-≈
d_'8818''45'resp'45''8776'_502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_502 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'45''8776'_502 v6
du_'8818''45'resp'45''8776'_502 ::
  T_IsDecTotalOrder_460 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_502 v0
  = let v1 = d_isTotalOrder_470 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_412 (coe v1) in
       coe
         (coe
            du_'8818''45'resp'45''8776'_112 (coe d_isPreorder_182 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_504 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'691''45''8776'_504 v6
du_'8818''45'resp'691''45''8776'_504 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_504 v0
  = let v1 = d_isTotalOrder_470 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_412 (coe v1) in
       coe
         (coe
            du_'8818''45'resp'691''45''8776'_106
            (coe d_isPreorder_182 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8818''45'resp'737''45''8776'_506 v6
du_'8818''45'resp'737''45''8776'_506 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_506 v0
  = let v1 = d_isTotalOrder_470 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_412 (coe v1) in
       coe
         (coe
            du_'8818''45'resp'737''45''8776'_100
            (coe d_isPreorder_182 (coe v2))))
-- Relation.Binary.Structures.IsDecTotalOrder.isDecPartialOrder
d_isDecPartialOrder_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 -> T_IsDecPartialOrder_224
d_isDecPartialOrder_508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecPartialOrder_508 v6
du_isDecPartialOrder_508 ::
  T_IsDecTotalOrder_460 -> T_IsDecPartialOrder_224
du_isDecPartialOrder_508 v0
  = coe
      C_IsDecPartialOrder'46'constructor_11683
      (coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0)))
      (coe d__'8799'__472 (coe v0)) (coe d__'8804''63'__474 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder.Eq.isDecEquivalence
d_isDecEquivalence_512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 -> T_IsDecEquivalence_44
d_isDecEquivalence_512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_512 v6
du_isDecEquivalence_512 ::
  T_IsDecTotalOrder_460 -> T_IsDecEquivalence_44
du_isDecEquivalence_512 v0
  = coe
      C_IsDecEquivalence'46'constructor_3083
      (coe
         d_isEquivalence_80
         (coe
            d_isPreorder_182
            (coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0)))))
      (coe d__'8799'__472 (coe v0))
-- Relation.Binary.Structures.IsDecTotalOrder.Eq._._≟_
d__'8799'__516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__516 v6
du__'8799'__516 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__516 v0 = coe d__'8799'__472 (coe v0)
-- Relation.Binary.Structures.IsDecTotalOrder.Eq._.isEquivalence
d_isEquivalence_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 -> T_IsEquivalence_26
d_isEquivalence_518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_518 v6
du_isEquivalence_518 :: T_IsDecTotalOrder_460 -> T_IsEquivalence_26
du_isEquivalence_518 v0
  = coe
      d_isEquivalence_80
      (coe
         d_isPreorder_182
         (coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0))))
-- Relation.Binary.Structures.IsDecTotalOrder.Eq._.isPartialEquivalence
d_isPartialEquivalence_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_520 v6
du_isPartialEquivalence_520 ::
  T_IsDecTotalOrder_460 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_520 v0
  = let v1 = coe du_isDecEquivalence_512 (coe v0) in
    coe
      (coe du_isPartialEquivalence_42 (coe d_isEquivalence_50 (coe v1)))
-- Relation.Binary.Structures.IsDecTotalOrder.Eq._.refl
d_refl_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 -> AgdaAny -> AgdaAny
d_refl_522 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_522 v6
du_refl_522 :: T_IsDecTotalOrder_460 -> AgdaAny -> AgdaAny
du_refl_522 v0
  = coe
      d_refl_34
      (coe
         d_isEquivalence_80
         (coe
            d_isPreorder_182
            (coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0)))))
-- Relation.Binary.Structures.IsDecTotalOrder.Eq._.reflexive
d_reflexive_524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_524 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_524 v6
du_reflexive_524 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_524 v0
  = let v1 = coe du_isDecEquivalence_512 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_40 (coe d_isEquivalence_50 (coe v1)) v2)
-- Relation.Binary.Structures.IsDecTotalOrder.Eq._.sym
d_sym_526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_526 v6
du_sym_526 ::
  T_IsDecTotalOrder_460 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_526 v0
  = coe
      d_sym_36
      (coe
         d_isEquivalence_80
         (coe
            d_isPreorder_182
            (coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0)))))
-- Relation.Binary.Structures.IsDecTotalOrder.Eq._.trans
d_trans_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_528 v6
du_trans_528 ::
  T_IsDecTotalOrder_460 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_528 v0
  = coe
      d_trans_38
      (coe
         d_isEquivalence_80
         (coe
            d_isPreorder_182
            (coe d_isPartialOrder_412 (coe d_isTotalOrder_470 (coe v0)))))
-- Relation.Binary.Structures.IsStrictTotalOrder
d_IsStrictTotalOrder_534 a0 a1 a2 a3 a4 a5 = ()
data T_IsStrictTotalOrder_534
  = C_IsStrictTotalOrder'46'constructor_24953 T_IsStrictPartialOrder_290
                                              (AgdaAny ->
                                               AgdaAny ->
                                               MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158)
-- Relation.Binary.Structures.IsStrictTotalOrder.isStrictPartialOrder
d_isStrictPartialOrder_542 ::
  T_IsStrictTotalOrder_534 -> T_IsStrictPartialOrder_290
d_isStrictPartialOrder_542 v0
  = case coe v0 of
      C_IsStrictTotalOrder'46'constructor_24953 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsStrictTotalOrder.compare
d_compare_544 ::
  T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_544 v0
  = case coe v0 of
      C_IsStrictTotalOrder'46'constructor_24953 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsStrictTotalOrder._.<-resp-≈
d_'60''45'resp'45''8776'_548 ::
  T_IsStrictTotalOrder_534 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_548 v0
  = coe
      d_'60''45'resp'45''8776'_308
      (coe d_isStrictPartialOrder_542 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'691''45''8776'_550 v6
du_'60''45'resp'691''45''8776'_550 ::
  T_IsStrictTotalOrder_534 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_550 v0
  = coe
      du_'60''45'resp'691''45''8776'_328
      (coe d_isStrictPartialOrder_542 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_552 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'737''45''8776'_552 v6
du_'60''45'resp'737''45''8776'_552 ::
  T_IsStrictTotalOrder_534 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_552 v0
  = coe
      du_'60''45'resp'737''45''8776'_330
      (coe d_isStrictPartialOrder_542 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._.asym
d_asym_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_554 = erased
-- Relation.Binary.Structures.IsStrictTotalOrder._.irrefl
d_irrefl_556 ::
  T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_556 = erased
-- Relation.Binary.Structures.IsStrictTotalOrder._.isEquivalence
d_isEquivalence_558 ::
  T_IsStrictTotalOrder_534 -> T_IsEquivalence_26
d_isEquivalence_558 v0
  = coe d_isEquivalence_302 (coe d_isStrictPartialOrder_542 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._.trans
d_trans_560 ::
  T_IsStrictTotalOrder_534 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_560 v0
  = coe d_trans_306 (coe d_isStrictPartialOrder_542 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._≟_
d__'8799'__562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__562 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__562 v6
du__'8799'__562 ::
  T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__562 v0
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_tri'8658'dec'8776'_492
      (coe d_compare_544 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder._<?_
d__'60''63'__564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'60''63'__564 v6
du__'60''63'__564 ::
  T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'60''63'__564 v0
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_tri'8658'dec'60'_528
      (coe d_compare_544 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder.isDecStrictPartialOrder
d_isDecStrictPartialOrder_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 -> T_IsDecStrictPartialOrder_336
d_isDecStrictPartialOrder_566 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecStrictPartialOrder_566 v6
du_isDecStrictPartialOrder_566 ::
  T_IsStrictTotalOrder_534 -> T_IsDecStrictPartialOrder_336
du_isDecStrictPartialOrder_566 v0
  = coe
      C_IsDecStrictPartialOrder'46'constructor_18663
      (coe d_isStrictPartialOrder_542 (coe v0))
      (coe du__'8799'__562 (coe v0)) (coe du__'60''63'__564 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq.isDecEquivalence
d_isDecEquivalence_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 -> T_IsDecEquivalence_44
d_isDecEquivalence_570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_570 v6
du_isDecEquivalence_570 ::
  T_IsStrictTotalOrder_534 -> T_IsDecEquivalence_44
du_isDecEquivalence_570 v0
  = coe
      C_IsDecEquivalence'46'constructor_3083
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_542 (coe v0)))
      (coe du__'8799'__562 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._._≟_
d__'8799'__574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__574 v6
du__'8799'__574 ::
  T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__574 v0 = coe du__'8799'__562 (coe v0)
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.isEquivalence
d_isEquivalence_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 -> T_IsEquivalence_26
d_isEquivalence_576 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_576 v6
du_isEquivalence_576 ::
  T_IsStrictTotalOrder_534 -> T_IsEquivalence_26
du_isEquivalence_576 v0
  = coe d_isEquivalence_302 (coe d_isStrictPartialOrder_542 (coe v0))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.isPartialEquivalence
d_isPartialEquivalence_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_578 v6
du_isPartialEquivalence_578 ::
  T_IsStrictTotalOrder_534 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_578 v0
  = let v1 = coe du_isDecEquivalence_570 (coe v0) in
    coe
      (coe du_isPartialEquivalence_42 (coe d_isEquivalence_50 (coe v1)))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.refl
d_refl_580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 -> AgdaAny -> AgdaAny
d_refl_580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_580 v6
du_refl_580 :: T_IsStrictTotalOrder_534 -> AgdaAny -> AgdaAny
du_refl_580 v0
  = coe
      d_refl_34
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_542 (coe v0)))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.reflexive
d_reflexive_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_582 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_582 v6
du_reflexive_582 ::
  T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_582 v0
  = let v1 = coe du_isDecEquivalence_570 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe du_reflexive_40 (coe d_isEquivalence_50 (coe v1)) v2)
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.sym
d_sym_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_584 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_584 v6
du_sym_584 ::
  T_IsStrictTotalOrder_534 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_584 v0
  = coe
      d_sym_36
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_542 (coe v0)))
-- Relation.Binary.Structures.IsStrictTotalOrder.Eq._.trans
d_trans_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_586 v6
du_trans_586 ::
  T_IsStrictTotalOrder_534 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_586 v0
  = coe
      d_trans_38
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_542 (coe v0)))
-- Relation.Binary.Structures.IsStrictTotalOrder.isDecEquivalence
d_isDecEquivalence_588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder_534 -> T_IsDecEquivalence_44
d_isDecEquivalence_588 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_588 v6
du_isDecEquivalence_588 ::
  T_IsStrictTotalOrder_534 -> T_IsDecEquivalence_44
du_isDecEquivalence_588 v0
  = coe
      C_IsDecEquivalence'46'constructor_3083
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_542 (coe v0)))
      (coe du__'8799'__562 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder
d_IsDenseLinearOrder_594 a0 a1 a2 a3 a4 a5 = ()
data T_IsDenseLinearOrder_594
  = C_IsDenseLinearOrder'46'constructor_28131 T_IsStrictTotalOrder_534
                                              (AgdaAny ->
                                               AgdaAny ->
                                               AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Structures.IsDenseLinearOrder.isStrictTotalOrder
d_isStrictTotalOrder_602 ::
  T_IsDenseLinearOrder_594 -> T_IsStrictTotalOrder_534
d_isStrictTotalOrder_602 v0
  = case coe v0 of
      C_IsDenseLinearOrder'46'constructor_28131 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDenseLinearOrder.dense
d_dense_604 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dense_604 v0
  = case coe v0 of
      C_IsDenseLinearOrder'46'constructor_28131 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsDenseLinearOrder._._<?_
d__'60''63'__608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'60''63'__608 v6
du__'60''63'__608 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'60''63'__608 v0
  = coe du__'60''63'__564 (coe d_isStrictTotalOrder_602 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._._≟_
d__'8799'__610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__610 v6
du__'8799'__610 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__610 v0
  = coe du__'8799'__562 (coe d_isStrictTotalOrder_602 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.<-resp-≈
d_'60''45'resp'45''8776'_612 ::
  T_IsDenseLinearOrder_594 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_612 v0
  = coe
      d_'60''45'resp'45''8776'_308
      (coe
         d_isStrictPartialOrder_542 (coe d_isStrictTotalOrder_602 (coe v0)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.<-respʳ-≈
d_'60''45'resp'691''45''8776'_614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'691''45''8776'_614 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'691''45''8776'_614 v6
du_'60''45'resp'691''45''8776'_614 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'691''45''8776'_614 v0
  = let v1 = d_isStrictTotalOrder_602 (coe v0) in
    coe
      (coe
         du_'60''45'resp'691''45''8776'_328
         (coe d_isStrictPartialOrder_542 (coe v1)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.<-respˡ-≈
d_'60''45'resp'737''45''8776'_616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'60''45'resp'737''45''8776'_616 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'737''45''8776'_616 v6
du_'60''45'resp'737''45''8776'_616 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'60''45'resp'737''45''8776'_616 v0
  = let v1 = d_isStrictTotalOrder_602 (coe v0) in
    coe
      (coe
         du_'60''45'resp'737''45''8776'_330
         (coe d_isStrictPartialOrder_542 (coe v1)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.asym
d_asym_618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_618 = erased
-- Relation.Binary.Structures.IsDenseLinearOrder._.compare
d_compare_620 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_620 v0
  = coe d_compare_544 (coe d_isStrictTotalOrder_602 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.irrefl
d_irrefl_622 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_622 = erased
-- Relation.Binary.Structures.IsDenseLinearOrder._.isDecEquivalence
d_isDecEquivalence_624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 -> T_IsDecEquivalence_44
d_isDecEquivalence_624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_624 v6
du_isDecEquivalence_624 ::
  T_IsDenseLinearOrder_594 -> T_IsDecEquivalence_44
du_isDecEquivalence_624 v0
  = coe
      du_isDecEquivalence_588 (coe d_isStrictTotalOrder_602 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.isDecStrictPartialOrder
d_isDecStrictPartialOrder_626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 -> T_IsDecStrictPartialOrder_336
d_isDecStrictPartialOrder_626 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecStrictPartialOrder_626 v6
du_isDecStrictPartialOrder_626 ::
  T_IsDenseLinearOrder_594 -> T_IsDecStrictPartialOrder_336
du_isDecStrictPartialOrder_626 v0
  = coe
      du_isDecStrictPartialOrder_566
      (coe d_isStrictTotalOrder_602 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.isEquivalence
d_isEquivalence_628 ::
  T_IsDenseLinearOrder_594 -> T_IsEquivalence_26
d_isEquivalence_628 v0
  = coe
      d_isEquivalence_302
      (coe
         d_isStrictPartialOrder_542 (coe d_isStrictTotalOrder_602 (coe v0)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.isStrictPartialOrder
d_isStrictPartialOrder_630 ::
  T_IsDenseLinearOrder_594 -> T_IsStrictPartialOrder_290
d_isStrictPartialOrder_630 v0
  = coe
      d_isStrictPartialOrder_542 (coe d_isStrictTotalOrder_602 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.trans
d_trans_632 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_632 v0
  = coe
      d_trans_306
      (coe
         d_isStrictPartialOrder_542 (coe d_isStrictTotalOrder_602 (coe v0)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq._≟_
d__'8799'__636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8799'__636 v6
du__'8799'__636 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__636 v0
  = let v1 = d_isStrictTotalOrder_602 (coe v0) in
    coe (coe du__'8799'__562 (coe v1))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.isDecEquivalence
d_isDecEquivalence_638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 -> T_IsDecEquivalence_44
d_isDecEquivalence_638 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecEquivalence_638 v6
du_isDecEquivalence_638 ::
  T_IsDenseLinearOrder_594 -> T_IsDecEquivalence_44
du_isDecEquivalence_638 v0
  = coe
      du_isDecEquivalence_570 (coe d_isStrictTotalOrder_602 (coe v0))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.isEquivalence
d_isEquivalence_640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 -> T_IsEquivalence_26
d_isEquivalence_640 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_640 v6
du_isEquivalence_640 ::
  T_IsDenseLinearOrder_594 -> T_IsEquivalence_26
du_isEquivalence_640 v0
  = let v1 = d_isStrictTotalOrder_602 (coe v0) in
    coe
      (coe d_isEquivalence_302 (coe d_isStrictPartialOrder_542 (coe v1)))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.isPartialEquivalence
d_isPartialEquivalence_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 -> T_IsPartialEquivalence_16
d_isPartialEquivalence_642 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_642 v6
du_isPartialEquivalence_642 ::
  T_IsDenseLinearOrder_594 -> T_IsPartialEquivalence_16
du_isPartialEquivalence_642 v0
  = let v1 = d_isStrictTotalOrder_602 (coe v0) in
    coe
      (let v2 = coe du_isDecEquivalence_570 (coe v1) in
       coe
         (coe du_isPartialEquivalence_42 (coe d_isEquivalence_50 (coe v2))))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.refl
d_refl_644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 -> AgdaAny -> AgdaAny
d_refl_644 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_644 v6
du_refl_644 :: T_IsDenseLinearOrder_594 -> AgdaAny -> AgdaAny
du_refl_644 v0
  = let v1 = d_isStrictTotalOrder_602 (coe v0) in
    coe
      (coe
         d_refl_34
         (coe
            d_isEquivalence_302 (coe d_isStrictPartialOrder_542 (coe v1))))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.reflexive
d_reflexive_646 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_646 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_646 v6
du_reflexive_646 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_646 v0
  = let v1 = d_isStrictTotalOrder_602 (coe v0) in
    coe
      (let v2 = coe du_isDecEquivalence_570 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe du_reflexive_40 (coe d_isEquivalence_50 (coe v2)) v3))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.sym
d_sym_648 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_648 v6
du_sym_648 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_648 v0
  = let v1 = d_isStrictTotalOrder_602 (coe v0) in
    coe
      (coe
         d_sym_36
         (coe
            d_isEquivalence_302 (coe d_isStrictPartialOrder_542 (coe v1))))
-- Relation.Binary.Structures.IsDenseLinearOrder._.Eq.trans
d_trans_650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsDenseLinearOrder_594 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_650 v6
du_trans_650 ::
  T_IsDenseLinearOrder_594 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_650 v0
  = let v1 = d_isStrictTotalOrder_602 (coe v0) in
    coe
      (coe
         d_trans_38
         (coe
            d_isEquivalence_302 (coe d_isStrictPartialOrder_542 (coe v1))))
-- Relation.Binary.Structures.IsApartnessRelation
d_IsApartnessRelation_656 a0 a1 a2 a3 a4 a5 = ()
data T_IsApartnessRelation_656
  = C_IsApartnessRelation'46'constructor_30225 (AgdaAny ->
                                                AgdaAny -> AgdaAny -> AgdaAny)
                                               (AgdaAny ->
                                                AgdaAny ->
                                                AgdaAny ->
                                                AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
-- Relation.Binary.Structures.IsApartnessRelation.irrefl
d_irrefl_666 ::
  T_IsApartnessRelation_656 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_666 = erased
-- Relation.Binary.Structures.IsApartnessRelation.sym
d_sym_668 ::
  T_IsApartnessRelation_656 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_668 v0
  = case coe v0 of
      C_IsApartnessRelation'46'constructor_30225 v2 v3 -> coe v2
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsApartnessRelation.cotrans
d_cotrans_670 ::
  T_IsApartnessRelation_656 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cotrans_670 v0
  = case coe v0 of
      C_IsApartnessRelation'46'constructor_30225 v2 v3 -> coe v3
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.IsApartnessRelation._¬#_
d__'172''35'__672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsApartnessRelation_656 -> AgdaAny -> AgdaAny -> ()
d__'172''35'__672 = erased
