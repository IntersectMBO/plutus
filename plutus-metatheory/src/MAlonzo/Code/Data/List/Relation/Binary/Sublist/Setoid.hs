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

module MAlonzo.Code.Data.List.Relation.Binary.Sublist.Setoid where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous
import qualified MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core
import qualified MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Data.List.Relation.Binary.Sublist.Setoid._._≋_
d__'8779'__44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8779'__44 = erased
-- Data.List.Relation.Binary.Sublist.Setoid._⊆_
d__'8838'__102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8838'__102 = erased
-- Data.List.Relation.Binary.Sublist.Setoid._⊇_
d__'8839'__104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8839'__104 = erased
-- Data.List.Relation.Binary.Sublist.Setoid._⊂_
d__'8834'__110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8834'__110 = erased
-- Data.List.Relation.Binary.Sublist.Setoid._⊃_
d__'8835'__116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8835'__116 = erased
-- Data.List.Relation.Binary.Sublist.Setoid._⊈_
d__'8840'__122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8840'__122 = erased
-- Data.List.Relation.Binary.Sublist.Setoid._⊉_
d__'8841'__128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8841'__128 = erased
-- Data.List.Relation.Binary.Sublist.Setoid._⊄_
d__'8836'__134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8836'__134 = erased
-- Data.List.Relation.Binary.Sublist.Setoid._⊅_
d__'8837'__140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8837'__140 = erased
-- Data.List.Relation.Binary.Sublist.Setoid._.Disjoint
d_Disjoint_168 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Data.List.Relation.Binary.Sublist.Setoid._.DisjointUnion
d_DisjointUnion_170 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Data.List.Relation.Binary.Sublist.Setoid._.fromAny
d_fromAny_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_fromAny_172 ~v0 ~v1 ~v2 = du_fromAny_172
du_fromAny_172 ::
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_fromAny_172 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_fromAny_74
      v1 v2
-- Data.List.Relation.Binary.Sublist.Setoid._.lookup
d_lookup_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_lookup_174 ~v0 ~v1 ~v2 = du_lookup_174
du_lookup_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_lookup_174 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_lookup_98
      v4 v5 v6 v7 v8
-- Data.List.Relation.Binary.Sublist.Setoid._.map
d_map_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_map_176 ~v0 ~v1 ~v2 = du_map_176
du_map_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_map_176 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_map_32
      v2 v3 v4 v5
-- Data.List.Relation.Binary.Sublist.Setoid._.minimum
d_minimum_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_minimum_178 ~v0 ~v1 ~v2 = du_minimum_178
du_minimum_178 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_minimum_178
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_minimum_48
-- Data.List.Relation.Binary.Sublist.Setoid._.toAny
d_toAny_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_toAny_180 ~v0 ~v1 ~v2 = du_toAny_180
du_toAny_180 ::
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_toAny_180 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_toAny_60
      v2 v3
-- Data.List.Relation.Binary.Sublist.Setoid.⊆-reflexive
d_'8838''45'reflexive_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'8838''45'reflexive_202 ~v0 ~v1 ~v2 v3 v4
  = du_'8838''45'reflexive_202 v3 v4
du_'8838''45'reflexive_202 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'8838''45'reflexive_202 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_fromPointwise_126
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Sublist.Setoid._.refl
d_refl_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_refl_206 ~v0 ~v1 v2 = du_refl_206 v2
du_refl_206 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_refl_206 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
-- Data.List.Relation.Binary.Sublist.Setoid._.trans
d_trans_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_trans_210 ~v0 ~v1 v2 = du_trans_210 v2
du_trans_210 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_trans_210 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_trans_1140
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
-- Data.List.Relation.Binary.Sublist.Setoid._.antisym
d_antisym_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_antisym_218 ~v0 ~v1 ~v2 = du_antisym_218
du_antisym_218 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_antisym_218
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_antisym_1184
      (coe (\ v0 v1 v2 v3 -> v2))
-- Data.List.Relation.Binary.Sublist.Setoid.⊆-isPreorder
d_'8838''45'isPreorder_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8838''45'isPreorder_220 ~v0 ~v1 v2
  = du_'8838''45'isPreorder_220 v2
du_'8838''45'isPreorder_220 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_'8838''45'isPreorder_220 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
         (coe
            MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
            (coe v0)))
      (coe du_'8838''45'reflexive_202)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_trans_1140
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
-- Data.List.Relation.Binary.Sublist.Setoid.⊆-isPartialOrder
d_'8838''45'isPartialOrder_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_236
d_'8838''45'isPartialOrder_222 ~v0 ~v1 v2
  = du_'8838''45'isPartialOrder_222 v2
du_'8838''45'isPartialOrder_222 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_236
du_'8838''45'isPartialOrder_222 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_11935
      (coe du_'8838''45'isPreorder_220 (coe v0))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_antisym_1184
         (coe (\ v1 v2 v3 v4 -> v3)))
-- Data.List.Relation.Binary.Sublist.Setoid.⊆-preorder
d_'8838''45'preorder_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_136
d_'8838''45'preorder_224 ~v0 ~v1 v2 = du_'8838''45'preorder_224 v2
du_'8838''45'preorder_224 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_136
du_'8838''45'preorder_224 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2331
      (coe du_'8838''45'isPreorder_220 (coe v0))
-- Data.List.Relation.Binary.Sublist.Setoid.⊆-poset
d_'8838''45'poset_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480
d_'8838''45'poset_226 ~v0 ~v1 v2 = du_'8838''45'poset_226 v2
du_'8838''45'poset_226 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480
du_'8838''45'poset_226 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_9149
      (coe du_'8838''45'isPartialOrder_222 (coe v0))
-- Data.List.Relation.Binary.Sublist.Setoid.RawPushout
d_RawPushout_238 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_RawPushout_238
  = C_RawPushout'46'constructor_4793 [AgdaAny]
                                     MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
                                     MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
-- Data.List.Relation.Binary.Sublist.Setoid.RawPushout.upperBound
d_upperBound_256 :: T_RawPushout_238 -> [AgdaAny]
d_upperBound_256 v0
  = case coe v0 of
      C_RawPushout'46'constructor_4793 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid.RawPushout.leg₁
d_leg'8321'_258 ::
  T_RawPushout_238 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_leg'8321'_258 v0
  = case coe v0 of
      C_RawPushout'46'constructor_4793 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid.RawPushout.leg₂
d_leg'8322'_260 ::
  T_RawPushout_238 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_leg'8322'_260 v0
  = case coe v0 of
      C_RawPushout'46'constructor_4793 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid._∷ʳ₁_
d__'8759''691''8321'__274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny -> T_RawPushout_238 -> T_RawPushout_238
d__'8759''691''8321'__274 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du__'8759''691''8321'__274 v2 v8 v9
du__'8759''691''8321'__274 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> T_RawPushout_238 -> T_RawPushout_238
du__'8759''691''8321'__274 v0 v1 v2
  = coe
      C_RawPushout'46'constructor_4793
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
         (coe d_upperBound_256 (coe v2)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
            v1)
         (d_leg'8321'_258 (coe v2)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36
         (d_leg'8322'_260 (coe v2)))
-- Data.List.Relation.Binary.Sublist.Setoid._∷ʳ₂_
d__'8759''691''8322'__292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny -> T_RawPushout_238 -> T_RawPushout_238
d__'8759''691''8322'__292 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du__'8759''691''8322'__292 v2 v8 v9
du__'8759''691''8322'__292 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> T_RawPushout_238 -> T_RawPushout_238
du__'8759''691''8322'__292 v0 v1 v2
  = coe
      C_RawPushout'46'constructor_4793
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
         (coe d_upperBound_256 (coe v2)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36
         (d_leg'8321'_258 (coe v2)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
            v1)
         (d_leg'8322'_260 (coe v2)))
-- Data.List.Relation.Binary.Sublist.Setoid.∷-rpo
d_'8759''45'rpo_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny -> AgdaAny -> T_RawPushout_238 -> T_RawPushout_238
d_'8759''45'rpo_318 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                    v12 v13
  = du_'8759''45'rpo_318 v2 v3 v4 v5 v11 v12 v13
du_'8759''45'rpo_318 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T_RawPushout_238 -> T_RawPushout_238
du_'8759''45'rpo_318 v0 v1 v2 v3 v4 v5 v6
  = coe
      C_RawPushout'46'constructor_4793
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
         (coe d_upperBound_256 (coe v6)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
            v1 v2 v4)
         (d_leg'8321'_258 (coe v6)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
            v1 v3 v5)
         (d_leg'8322'_260 (coe v6)))
-- Data.List.Relation.Binary.Sublist.Setoid.⊆-pushoutˡ
d_'8838''45'pushout'737'_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  T_RawPushout_238
d_'8838''45'pushout'737'_336 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'8838''45'pushout'737'_336 v2 v3 v4 v5 v6
du_'8838''45'pushout'737'_336 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  T_RawPushout_238
du_'8838''45'pushout'737'_336 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C_'91''93'_28
        -> coe
             (\ v5 ->
                coe
                  C_RawPushout'46'constructor_4793 (coe v3) (coe v5)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
                     (coe v3)))
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v8
        -> case coe v2 of
             (:) v9 v10
               -> coe
                    (\ v11 ->
                       coe
                         du__'8759''691''8321'__274 (coe v0) (coe v9)
                         (coe du_'8838''45'pushout'737'_336 v0 v1 v10 v3 v8 v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v2 of
                    (:) v13 v14
                      -> coe
                           (\ v15 ->
                              case coe v15 of
                                MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v19
                                  -> case coe v3 of
                                       (:) v20 v21
                                         -> coe
                                              du__'8759''691''8322'__292 (coe v0) (coe v20)
                                              (coe
                                                 du_'8838''45'pushout'737'_336 v0 v1 v2 v21
                                                 (coe
                                                    MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
                                                    v9 v10)
                                                 v19)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v20 v21
                                  -> case coe v3 of
                                       (:) v22 v23
                                         -> coe
                                              du_'8759''45'rpo_318 (coe v0) (coe v11) (coe v13)
                                              (coe v22) (coe v9) (coe v20)
                                              (coe
                                                 du_'8838''45'pushout'737'_336 v0 v12 v14 v23 v10
                                                 v21)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid.⊆-joinˡ
d_'8838''45'join'737'_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8838''45'join'737'_372 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8838''45'join'737'_372 v2 v3 v4 v5 v6 v7
du_'8838''45'join'737'_372 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8838''45'join'737'_372 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         d_upperBound_256
         (coe
            du_rpo_382 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_trans_1140
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
         (coe v1) (coe v2)
         (coe
            d_upperBound_256
            (coe
               du_rpo_382 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
         (coe v4)
         (coe
            d_leg'8321'_258
            (coe
               du_rpo_382 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))))
-- Data.List.Relation.Binary.Sublist.Setoid._.rpo
d_rpo_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  T_RawPushout_238
d_rpo_382 ~v0 ~v1 v2 v3 v4 v5 v6 v7 = du_rpo_382 v2 v3 v4 v5 v6 v7
du_rpo_382 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  T_RawPushout_238
du_rpo_382 v0 v1 v2 v3 v4 v5
  = coe du_'8838''45'pushout'737'_336 v0 v1 v2 v3 v4 v5
-- Data.List.Relation.Binary.Sublist.Setoid.UpperBound
d_UpperBound_394 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_UpperBound_394
  = C_UpperBound'46'constructor_34613 [AgdaAny]
                                      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
                                      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
                                      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
-- Data.List.Relation.Binary.Sublist.Setoid.UpperBound.theUpperBound
d_theUpperBound_414 :: T_UpperBound_394 -> [AgdaAny]
d_theUpperBound_414 v0
  = case coe v0 of
      C_UpperBound'46'constructor_34613 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid.UpperBound.sub
d_sub_416 ::
  T_UpperBound_394 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_sub_416 v0
  = case coe v0 of
      C_UpperBound'46'constructor_34613 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid.UpperBound.inj₁
d_inj'8321'_418 ::
  T_UpperBound_394 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_inj'8321'_418 v0
  = case coe v0 of
      C_UpperBound'46'constructor_34613 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid.UpperBound.inj₂
d_inj'8322'_420 ::
  T_UpperBound_394 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_inj'8322'_420 v0
  = case coe v0 of
      C_UpperBound'46'constructor_34613 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid.∷ₙ-ub
d_'8759''8345''45'ub_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny -> T_UpperBound_394 -> T_UpperBound_394
d_'8759''8345''45'ub_434 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8759''8345''45'ub_434 v9
du_'8759''8345''45'ub_434 :: T_UpperBound_394 -> T_UpperBound_394
du_'8759''8345''45'ub_434 v0
  = coe
      C_UpperBound'46'constructor_34613
      (coe d_theUpperBound_414 (coe v0))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36
         (d_sub_416 (coe v0)))
      (coe d_inj'8321'_418 (coe v0)) (coe d_inj'8322'_420 (coe v0))
-- Data.List.Relation.Binary.Sublist.Setoid._∷ₗ-ub_
d__'8759''8343''45'ub__454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T_UpperBound_394 -> T_UpperBound_394
d__'8759''8343''45'ub__454 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                           v10 v11
  = du__'8759''8343''45'ub__454 v2 v9 v10 v11
du__'8759''8343''45'ub__454 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> T_UpperBound_394 -> T_UpperBound_394
du__'8759''8343''45'ub__454 v0 v1 v2 v3
  = coe
      C_UpperBound'46'constructor_34613
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
         (coe d_theUpperBound_414 (coe v3)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
            v1)
         (d_sub_416 (coe v3)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
         v2 (d_inj'8321'_418 (coe v3)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36
         (d_inj'8322'_420 (coe v3)))
-- Data.List.Relation.Binary.Sublist.Setoid._∷ᵣ-ub_
d__'8759''7523''45'ub__476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T_UpperBound_394 -> T_UpperBound_394
d__'8759''7523''45'ub__476 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                           v10 v11
  = du__'8759''7523''45'ub__476 v2 v9 v10 v11
du__'8759''7523''45'ub__476 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> T_UpperBound_394 -> T_UpperBound_394
du__'8759''7523''45'ub__476 v0 v1 v2 v3
  = coe
      C_UpperBound'46'constructor_34613
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
         (coe d_theUpperBound_414 (coe v3)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
            v1)
         (d_sub_416 (coe v3)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36
         (d_inj'8321'_418 (coe v3)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
         v2 (d_inj'8322'_420 (coe v3)))
-- Data.List.Relation.Binary.Sublist.Setoid._,_∷-ub_
d__'44'_'8759''45'ub__502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T_UpperBound_394 -> T_UpperBound_394
d__'44'_'8759''45'ub__502 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          v10 v11 v12 v13
  = du__'44'_'8759''45'ub__502 v2 v10 v11 v12 v13
du__'44'_'8759''45'ub__502 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T_UpperBound_394 -> T_UpperBound_394
du__'44'_'8759''45'ub__502 v0 v1 v2 v3 v4
  = coe
      C_UpperBound'46'constructor_34613
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
         (coe d_theUpperBound_414 (coe v4)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
            v1)
         (d_sub_416 (coe v4)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
         v2 (d_inj'8321'_418 (coe v4)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
         v3 (d_inj'8322'_420 (coe v4)))
-- Data.List.Relation.Binary.Sublist.Setoid.⊆-upper-bound
d_'8838''45'upper'45'bound_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  T_UpperBound_394
d_'8838''45'upper'45'bound_520 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8838''45'upper'45'bound_520 v2 v3 v4 v5 v6 v7
du_'8838''45'upper'45'bound_520 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  T_UpperBound_394
du_'8838''45'upper'45'bound_520 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C_'91''93'_28
        -> coe
             seq (coe v5)
             (coe
                C_UpperBound'46'constructor_34613
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)
                (coe v4) (coe v4))
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v9
        -> case coe v3 of
             (:) v10 v11
               -> case coe v5 of
                    MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v15
                      -> coe
                           du_'8759''8345''45'ub_434
                           (coe
                              du_'8838''45'upper'45'bound_520 (coe v0) (coe v1) (coe v2)
                              (coe v11) (coe v9) (coe v15))
                    MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v16 v17
                      -> case coe v2 of
                           (:) v18 v19
                             -> coe
                                  du__'8759''7523''45'ub__476 (coe v0) (coe v10) (coe v16)
                                  (coe
                                     du_'8838''45'upper'45'bound_520 (coe v0) (coe v1) (coe v19)
                                     (coe v11) (coe v9) (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v10 v11
        -> case coe v1 of
             (:) v12 v13
               -> case coe v3 of
                    (:) v14 v15
                      -> case coe v5 of
                           MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v19
                             -> coe
                                  du__'8759''8343''45'ub__454 (coe v0) (coe v14) (coe v10)
                                  (coe
                                     du_'8838''45'upper'45'bound_520 (coe v0) (coe v13) (coe v2)
                                     (coe v15) (coe v11) (coe v19))
                           MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v20 v21
                             -> case coe v2 of
                                  (:) v22 v23
                                    -> coe
                                         du__'44'_'8759''45'ub__502 (coe v0) (coe v14) (coe v10)
                                         (coe v20)
                                         (coe
                                            du_'8838''45'upper'45'bound_520 (coe v0) (coe v13)
                                            (coe v23) (coe v15) (coe v11) (coe v21))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid.⊆-disjoint-union
d_'8838''45'disjoint'45'union_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  T_UpperBound_394
d_'8838''45'disjoint'45'union_562 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_'8838''45'disjoint'45'union_562 v2 v3 v4 v5 v6 v7
du_'8838''45'disjoint'45'union_562 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  T_UpperBound_394
du_'8838''45'disjoint'45'union_562 v0 v1 v2 v3 v4 v5
  = coe
      du_'8838''45'upper'45'bound_520 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
-- Data.List.Relation.Binary.Sublist.Setoid._.Sublist
d_Sublist_2387 a0 a1 a2 a3 a4 = ()
