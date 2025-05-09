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

module MAlonzo.Code.Data.Tree.AVL.Indexed where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.List qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.DifferenceList qualified
import MAlonzo.Code.Data.Fin.Base qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.List.Base qualified
import MAlonzo.Code.Data.Tree.AVL.Height qualified
import MAlonzo.Code.Data.Tree.AVL.Key qualified
import MAlonzo.Code.Data.Tree.AVL.Value qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Tree.AVL.Indexed._._<_<_
d__'60'_'60'__102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) -> AgdaAny -> Maybe (Maybe AgdaAny) -> ()
d__'60'_'60'__102 = erased
-- Data.Tree.AVL.Indexed._._<⁺_
d__'60''8314'__104 a0 a1 a2 a3 a4 a5 = ()
-- Data.Tree.AVL.Indexed._._≈∙_
d__'8776''8729'__106 a0 a1 a2 a3 a4 a5 = ()
-- Data.Tree.AVL.Indexed._.Key⁺
d_Key'8314'_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 -> ()
d_Key'8314'_108 = erased
-- Data.Tree.AVL.Indexed._.irrefl⁺
d_irrefl'8314'_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl'8314'_110 = erased
-- Data.Tree.AVL.Indexed._.refl⁺
d_refl'8314'_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_refl'8314'_112 ~v0 ~v1 ~v2 v3 = du_refl'8314'_112 v3
du_refl'8314'_112 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_refl'8314'_112 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Key.du_refl'8314'_94 (coe v0)
-- Data.Tree.AVL.Indexed._.strictPartialOrder
d_strictPartialOrder_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_strictPartialOrder_114 ~v0 ~v1 ~v2 v3
  = du_strictPartialOrder_114 v3
du_strictPartialOrder_114 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
du_strictPartialOrder_114 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.Key.du_strictPartialOrder_118 (coe v0)
-- Data.Tree.AVL.Indexed._.strictTotalOrder
d_strictTotalOrder_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_strictTotalOrder_116 ~v0 ~v1 ~v2 v3 = du_strictTotalOrder_116 v3
du_strictTotalOrder_116 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
du_strictTotalOrder_116 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.Key.du_strictTotalOrder_202 (coe v0)
-- Data.Tree.AVL.Indexed._.sym⁺
d_sym'8314'_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_sym'8314'_118 ~v0 ~v1 ~v2 v3 = du_sym'8314'_118 v3
du_sym'8314'_118 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_sym'8314'_118 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Key.du_sym'8314'_100 (coe v0)
-- Data.Tree.AVL.Indexed._.trans⁺
d_trans'8314'_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
d_trans'8314'_120 ~v0 ~v1 ~v2 v3 = du_trans'8314'_120 v3
du_trans'8314'_120 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_trans'8314'_120 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Key.du_trans'8314'_108 (coe v0)
-- Data.Tree.AVL.Indexed._.⊥⁺<[_]<⊤⁺
d_'8869''8314''60''91'_'93''60''8868''8314'_122 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8869''8314''60''91'_'93''60''8868''8314'_122 ~v0 ~v1
  = du_'8869''8314''60''91'_'93''60''8868''8314'_122
du_'8869''8314''60''91'_'93''60''8868''8314'_122 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8869''8314''60''91'_'93''60''8868''8314'_122
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30)
-- Data.Tree.AVL.Indexed._.Extrema.[_]-injective
d_'91'_'93''45'injective_138 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'_'93''45'injective_138 = erased
-- Data.Tree.AVL.Indexed._.K&_
d_K'38'__144 a0 a1 a2 a3 a4 a5 = ()
-- Data.Tree.AVL.Indexed._.Value
d_Value_148 a0 a1 a2 a3 a4 = ()
-- Data.Tree.AVL.Indexed._.const
d_const_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38
d_const_150 ~v0 ~v1 ~v2 ~v3 = du_const_150
du_const_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38
du_const_150 v0 v1
  = coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94
-- Data.Tree.AVL.Indexed._.fromPair
d_fromPair_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56
d_fromPair_152 ~v0 ~v1 ~v2 ~v3 = du_fromPair_152
du_fromPair_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56
du_fromPair_152 v0 v1 v2
  = coe MAlonzo.Code.Data.Tree.AVL.Value.du_fromPair_86 v2
-- Data.Tree.AVL.Indexed._.key
d_key_154 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> AgdaAny
d_key_154 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v0)
-- Data.Tree.AVL.Indexed._.toPair
d_toPair_156 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_toPair_156 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v0))
      (coe MAlonzo.Code.Data.Tree.AVL.Value.d_value_68 (coe v0))
-- Data.Tree.AVL.Indexed._.value
d_value_158 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> AgdaAny
d_value_158 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_value_68 (coe v0)
-- Data.Tree.AVL.Indexed._.K&_.key
d_key_162 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> AgdaAny
d_key_162 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v0)
-- Data.Tree.AVL.Indexed._.K&_.value
d_value_164 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> AgdaAny
d_value_164 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_value_68 (coe v0)
-- Data.Tree.AVL.Indexed._.Value.family
d_family_168 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_family_168 = erased
-- Data.Tree.AVL.Indexed._.Value.respects
d_respects_170 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_respects_170 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_respects_48 (coe v0)
-- Data.Tree.AVL.Indexed.Tree
d_Tree_180 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_Tree_180
  = C_leaf_192 MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 |
    C_node_208 Integer Integer
               MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 T_Tree_180 T_Tree_180
               MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30
-- Data.Tree.AVL.Indexed._.ordered
d_ordered_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  T_Tree_180 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
d_ordered_224 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 ~v8 v9
  = du_ordered_224 v3 v6 v7 v9
du_ordered_224 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  T_Tree_180 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_ordered_224 v0 v1 v2 v3
  = case coe v3 of
      C_leaf_192 v4 -> coe v4
      C_node_208 v4 v5 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Data.Tree.AVL.Key.du_trans'8314'_108 v0 v1
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v7))))
             v2
             (coe
                du_ordered_224 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                      (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v7))))
                (coe v8))
             (coe
                du_ordered_224 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                      (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v7))))
                (coe v2) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.Val
d_Val_236 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Val_236 = erased
-- Data.Tree.AVL.Indexed._.V≈
d_V'8776'_238 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_V'8776'_238 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_respects_48 (coe v0)
-- Data.Tree.AVL.Indexed._.leaf-injective
d_leaf'45'injective_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leaf'45'injective_248 = erased
-- Data.Tree.AVL.Indexed._.node-injective-key
d_node'45'injective'45'key_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  T_Tree_180 ->
  T_Tree_180 ->
  T_Tree_180 ->
  T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_node'45'injective'45'key_280 = erased
-- Data.Tree.AVL.Indexed._.castˡ
d_cast'737'_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  T_Tree_180 -> T_Tree_180
d_cast'737'_290 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 ~v9 v10 v11
  = du_cast'737'_290 v3 v6 v7 v8 v10 v11
du_cast'737'_290 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  T_Tree_180 -> T_Tree_180
du_cast'737'_290 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_leaf_192 v6
        -> coe
             C_leaf_192
             (coe
                MAlonzo.Code.Data.Tree.AVL.Key.du_trans'8314'_108 v0 v1 v2 v3 v4
                v6)
      C_node_208 v6 v7 v9 v10 v11 v12
        -> coe
             C_node_208 v6 v7 v9
             (coe
                du_cast'737'_290 (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                      (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v9))))
                (coe v4) (coe v10))
             v11 v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.castʳ
d_cast'691'_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  T_Tree_180 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  T_Tree_180
d_cast'691'_316 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 ~v9 v10 v11
  = du_cast'691'_316 v3 v6 v7 v8 v10 v11
du_cast'691'_316 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  T_Tree_180 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  T_Tree_180
du_cast'691'_316 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_leaf_192 v6
        -> coe
             C_leaf_192
             (coe
                MAlonzo.Code.Data.Tree.AVL.Key.du_trans'8314'_108 v0 v1 v2 v3 v6
                v5)
      C_node_208 v6 v7 v9 v10 v11 v12
        -> coe
             C_node_208 v6 v7 v9 v10
             (coe
                du_cast'691'_316 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                      (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v9))))
                (coe v2) (coe v3) (coe v11) (coe v5))
             v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.joinˡ⁺
d_join'737''8314'_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_join'737''8314'_366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10
                      v11 v12 v13 v14
  = du_join'737''8314'_366 v8 v9 v11 v12 v13 v14
du_join'737''8314'_366 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_join'737''8314'_366 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                    (coe
                       C_node_208
                       (MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v0))
                       v1 v2 v7 v4 v5)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v9
               -> coe
                    seq (coe v9)
                    (case coe v5 of
                       MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                              (coe
                                 C_node_208
                                 (MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                    (coe v0))
                                 (addInt (coe (1 :: Integer)) (coe v0)) v2 v7 v4
                                 (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38))
                       MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Data.Fin.Base.C_suc_16
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                              (coe
                                 C_node_208
                                 (MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                    (coe v0))
                                 v0 v2 v7 v4
                                 (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42))
                       MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42
                         -> case coe v7 of
                              C_node_208 v11 v12 v14 v15 v16 v17
                                -> case coe v17 of
                                     MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34
                                       -> case coe v16 of
                                            C_node_208 v19 v20 v22 v23 v24 v25
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                   (coe
                                                      C_node_208
                                                      (addInt (coe (1 :: Integer)) (coe v1))
                                                      (addInt (coe (1 :: Integer)) (coe v1)) v22
                                                      (coe
                                                         C_node_208 v1 v19 v14 v15 v23
                                                         (coe
                                                            MAlonzo.Code.Data.Tree.AVL.Height.du_max'8764'_50
                                                            (coe v25)))
                                                      (coe
                                                         C_node_208 v20 v1 v2 v24 v4
                                                         (coe
                                                            MAlonzo.Code.Data.Tree.AVL.Height.du_'8764'max_58
                                                            (coe v25)))
                                                      (coe
                                                         MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                            (coe
                                               C_node_208 (addInt (coe (1 :: Integer)) (coe v1))
                                               (addInt (coe (2 :: Integer)) (coe v1)) v14 v15
                                               (coe
                                                  C_node_208 (addInt (coe (1 :: Integer)) (coe v1))
                                                  v1 v2 v16 v4
                                                  (coe
                                                     MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42))
                                               (coe
                                                  MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34))
                                     MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                            (coe
                                               C_node_208 (addInt (coe (1 :: Integer)) (coe v1))
                                               (addInt (coe (1 :: Integer)) (coe v1)) v14 v15
                                               (coe
                                                  C_node_208 v1 v1 v2 v16 v4
                                                  (coe
                                                     MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38))
                                               (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.joinʳ⁺
d_join'691''8314'_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_join'691''8314'_456 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10
                      v11 v12 v13 v14
  = du_join'691''8314'_456 v8 v9 v11 v12 v13 v14
du_join'691''8314'_456 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_join'691''8314'_456 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                    (coe
                       C_node_208 v0
                       (MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v1))
                       v2 v3 v7 v5)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v9
               -> coe
                    seq (coe v9)
                    (case coe v5 of
                       MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34
                         -> case coe v7 of
                              C_node_208 v11 v12 v14 v15 v16 v17
                                -> case coe v17 of
                                     MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                            (coe
                                               C_node_208 (addInt (coe (1 :: Integer)) (coe v0))
                                               (addInt (coe (1 :: Integer)) (coe v0)) v14
                                               (coe
                                                  C_node_208 v0 v0 v2 v3 v15
                                                  (coe
                                                     MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38))
                                               v16
                                               (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38))
                                     MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                            (coe
                                               C_node_208 (addInt (coe (2 :: Integer)) (coe v0))
                                               (addInt (coe (1 :: Integer)) (coe v0)) v14
                                               (coe
                                                  C_node_208 v0
                                                  (addInt (coe (1 :: Integer)) (coe v0)) v2 v3 v15
                                                  (coe
                                                     MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34))
                                               v16
                                               (coe
                                                  MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42))
                                     MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42
                                       -> case coe v15 of
                                            C_node_208 v19 v20 v22 v23 v24 v25
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                   (coe
                                                      C_node_208
                                                      (addInt (coe (1 :: Integer)) (coe v0))
                                                      (addInt (coe (1 :: Integer)) (coe v0)) v22
                                                      (coe
                                                         C_node_208 v0 v19 v2 v3 v23
                                                         (coe
                                                            MAlonzo.Code.Data.Tree.AVL.Height.du_max'8764'_50
                                                            (coe v25)))
                                                      (coe
                                                         C_node_208 v20 v0 v14 v24 v16
                                                         (coe
                                                            MAlonzo.Code.Data.Tree.AVL.Height.du_'8764'max_58
                                                            (coe v25)))
                                                      (coe
                                                         MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Data.Fin.Base.C_suc_16
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                              (coe
                                 C_node_208 v0
                                 (MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                    (coe v0))
                                 v2 v3 v7 (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34))
                       MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                              (coe
                                 C_node_208 (addInt (coe (1 :: Integer)) (coe v1))
                                 (MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                    (coe v1))
                                 v2 v3 v7 (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.joinˡ⁻
d_join'737''8315'_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_join'737''8315'_532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10
                      v11 v12 v13 v14
  = du_join'737''8315'_532 v8 v9 v11 v12 v13 v14
du_join'737''8315'_532 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_join'737''8315'_532 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      0 -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                           (coe
                              C_node_208
                              (MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe (0 :: Integer)))
                              v1 v2 v7 v4 v5)
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v9
                      -> coe
                           seq (coe v9)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Data.Fin.Base.C_suc_16
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                              (coe
                                 C_node_208
                                 (MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                    (coe (0 :: Integer)))
                                 v1 v2 v7 v4 v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Data.Fin.Base.C_zero_12
                         -> case coe v5 of
                              MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34
                                -> coe
                                     du_join'691''8314'_456
                                     (coe
                                        MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v0))
                                     (coe v0) (coe v2) (coe v8)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                        (coe v4))
                                     (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34)
                              MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                     (coe
                                        C_node_208
                                        (MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v0))
                                        v0 v2 v8 v4
                                        (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34))
                              MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                     (coe
                                        C_node_208
                                        (MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v0))
                                        v6 v2 v8 v4
                                        (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Data.Fin.Base.C_suc_16 v10
                         -> coe
                              seq (coe v10)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                 (coe
                                    C_node_208
                                    (MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                       (coe v0))
                                    v1 v2 v8 v4 v5))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Tree.AVL.Indexed._.joinʳ⁻
d_join'691''8315'_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_join'691''8315'_594 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10
                      v11 v12 v13 v14
  = du_join'691''8315'_594 v8 v9 v11 v12 v13 v14
du_join'691''8315'_594 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_join'691''8315'_594 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                           (coe
                              C_node_208 v0
                              (MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe (0 :: Integer)))
                              v2 v3 v7 v5)
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v9
                      -> coe
                           seq (coe v9)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Data.Fin.Base.C_suc_16
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                              (coe
                                 C_node_208 v0
                                 (MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                    (coe (0 :: Integer)))
                                 v2 v3 v7 v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Data.Fin.Base.C_zero_12
                         -> case coe v5 of
                              MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                     (coe
                                        C_node_208 v6
                                        (MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v1))
                                        v2 v3 v8
                                        (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38))
                              MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                     (coe
                                        C_node_208 v1
                                        (MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v1))
                                        v2 v3 v8
                                        (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42))
                              MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42
                                -> coe
                                     du_join'737''8314'_366 (coe v1)
                                     (coe
                                        MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v1))
                                     (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                        (coe v3))
                                     (coe v8)
                                     (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Data.Fin.Base.C_suc_16 v10
                         -> coe
                              seq (coe v10)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                 (coe
                                    C_node_208 v0
                                    (MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                       (coe v1))
                                    v2 v3 v8 v5))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Tree.AVL.Indexed._.headTail
d_headTail_648 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer -> T_Tree_180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_headTail_648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_headTail_648 v8 v9
du_headTail_648 ::
  Integer -> T_Tree_180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_headTail_648 v0 v1
  = case coe v1 of
      C_node_208 v2 v3 v5 v6 v7 v8
        -> let v9
                 = let v9 = subInt (coe v2) (coe (1 :: Integer)) in
                   coe
                     (let v10 = coe du_headTail_648 (coe v9) (coe v6) in
                      coe
                        (case coe v10 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                            (coe
                                               du_join'737''8315'_532 (coe v2) (coe v3) (coe v5)
                                               (coe v14) (coe v7) (coe v8)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)) in
           coe
             (case coe v6 of
                C_leaf_192 v10
                  -> let v11
                           = case coe v2 of
                               _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                                   let v11 = subInt (coe v2) (coe (1 :: Integer)) in
                                   coe
                                     (let v12 = coe du_headTail_648 (coe v11) (coe v6) in
                                      coe
                                        (case coe v12 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                             -> case coe v14 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v15)
                                                            (coe
                                                               du_join'737''8315'_532 (coe v2)
                                                               (coe v3) (coe v5) (coe v16) (coe v7)
                                                               (coe v8)))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                               _ -> coe v9 in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''43'_34
                            -> case coe v0 of
                                 _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
                                     case coe v3 of
                                       _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                                           coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe v10)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                   (coe v7)))
                                       _ -> coe v11
                                 _ -> coe v11
                          MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v7)))
                          _ -> coe v11)
                _ -> coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.initLast
d_initLast_698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer -> T_Tree_180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_initLast_698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_initLast_698 v8 v9
du_initLast_698 ::
  Integer -> T_Tree_180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_initLast_698 v0 v1
  = case coe v1 of
      C_node_208 v2 v3 v5 v6 v7 v8
        -> let v9
                 = let v9 = subInt (coe v3) (coe (1 :: Integer)) in
                   coe
                     (let v10 = coe du_initLast_698 (coe v9) (coe v7) in
                      coe
                        (case coe v10 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                            (coe
                                               du_join'691''8315'_594 (coe v2) (coe v3) (coe v5)
                                               (coe v6) (coe v14) (coe v8)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)) in
           coe
             (case coe v7 of
                C_leaf_192 v10
                  -> let v11
                           = case coe v3 of
                               _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                                   let v11 = subInt (coe v3) (coe (1 :: Integer)) in
                                   coe
                                     (let v12 = coe du_initLast_698 (coe v11) (coe v7) in
                                      coe
                                        (case coe v12 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                             -> case coe v14 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v15)
                                                            (coe
                                                               du_join'691''8315'_594 (coe v2)
                                                               (coe v3) (coe v5) (coe v6) (coe v16)
                                                               (coe v8)))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                               _ -> coe v9 in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v6)))
                          MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42
                            -> case coe v0 of
                                 _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
                                     coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v6)))
                                 _ -> coe v11
                          _ -> coe v11)
                _ -> coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.join
d_join_754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  T_Tree_180 ->
  T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_join_754 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du_join_754 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_join_754 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  T_Tree_180 ->
  T_Tree_180 ->
  MAlonzo.Code.Data.Tree.AVL.Height.T__'8764'_'8852'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_join_754 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = let v10
          = let v10 = subInt (coe v5) (coe (1 :: Integer)) in
            coe
              (let v11 = coe du_headTail_648 (coe v10) (coe v8) in
               coe
                 (case coe v11 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> case coe v13 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> coe
                                  du_join'691''8315'_594 (coe v4) (coe v5) (coe v12)
                                  (coe
                                     du_cast'691'_316 (coe v0) (coe v1) (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v12))))
                                     (coe v7) (coe v14))
                                  (coe v15) (coe v9)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError)) in
    coe
      (case coe v8 of
         C_leaf_192 v11
           -> let v12
                    = case coe v5 of
                        _ | coe geqInt (coe v5) (coe (1 :: Integer)) ->
                            let v12 = subInt (coe v5) (coe (1 :: Integer)) in
                            coe
                              (let v13 = coe du_headTail_648 (coe v12) (coe v8) in
                               coe
                                 (case coe v13 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                      -> case coe v15 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                             -> coe
                                                  du_join'691''8315'_594 (coe v4) (coe v5) (coe v14)
                                                  (coe
                                                     du_cast'691'_316 (coe v0) (coe v1) (coe v2)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                           (coe
                                                              MAlonzo.Code.Data.Tree.AVL.Value.d_key_66
                                                              (coe v14))))
                                                     (coe v7) (coe v16))
                                                  (coe v17) (coe v9)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                        _ -> coe v10 in
              coe
                (case coe v9 of
                   MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                          (coe
                             du_cast'691'_316 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                             (coe v11))
                   MAlonzo.Code.Data.Tree.AVL.Height.C_'8764''45'_42
                     -> case coe v6 of
                          _ | coe geqInt (coe v6) (coe (1 :: Integer)) ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                (coe
                                   du_cast'691'_316 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                                   (coe v11))
                          _ -> coe v12
                   _ -> coe v12)
         _ -> coe v10)
-- Data.Tree.AVL.Indexed._.empty
d_empty_790 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  T_Tree_180
d_empty_790 ~v0 ~v1 ~v2 = du_empty_790
du_empty_790 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  T_Tree_180
du_empty_790 = coe C_leaf_192
-- Data.Tree.AVL.Indexed._.singleton
d_singleton_798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Tree_180
d_singleton_798 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_singleton_798 v8 v9 v10
du_singleton_798 ::
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Tree_180
du_singleton_798 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             C_node_208 (0 :: Integer) (0 :: Integer)
             (coe
                MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 (coe v0) (coe v1))
             (coe C_leaf_192 (coe v3)) (coe C_leaf_192 (coe v4))
             (coe MAlonzo.Code.Data.Tree.AVL.Height.C_'8764'0_38)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.insertWith
d_insertWith_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_insertWith_818 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 v10 v11 v12
  = du_insertWith_818 v3 v5 v9 v10 v11 v12
du_insertWith_818 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_insertWith_818 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_leaf_192 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.Fin.Base.C_suc_16
                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
             (coe
                du_singleton_798 (coe v2)
                (coe v3 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                (coe v5))
      C_node_208 v6 v7 v9 v10 v11 v12
        -> case coe v9 of
             MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 v13 v14
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                      -> let v17
                               = coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_compare_544
                                   (MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                                      (coe v0))
                                   v2 v13 in
                         coe
                           (case coe v17 of
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v18
                                -> coe
                                     du_join'737''8314'_366 (coe v6) (coe v7) (coe v9)
                                     (coe
                                        du_insertWith_818 (coe v0) (coe v1) (coe v2) (coe v3)
                                        (coe v10)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                 v18))))
                                     (coe v11) (coe v12)
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v19
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                     (coe
                                        C_node_208 v6 v7
                                        (coe
                                           MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 (coe v13)
                                           (coe
                                              MAlonzo.Code.Data.Tree.AVL.Value.d_respects_48 v1 v2
                                              v13 v19
                                              (coe
                                                 v3
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                    (coe
                                                       MAlonzo.Code.Data.Tree.AVL.Value.d_respects_48
                                                       v1 v13 v2
                                                       (let v21
                                                              = coe
                                                                  MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
                                                                  (coe v0) in
                                                        coe
                                                          (let v22
                                                                 = coe
                                                                     MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728
                                                                     (coe v21) in
                                                           coe
                                                             (let v23
                                                                    = coe
                                                                        MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108
                                                                        (coe v22) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                                                   (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                      (coe v23))
                                                                   v2 v13 v19))))
                                                       v14)))))
                                        v10 v11 v12)
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v20
                                -> coe
                                     du_join'691''8314'_456 (coe v6) (coe v7) (coe v9) (coe v10)
                                     (coe
                                        du_insertWith_818 (coe v0) (coe v1) (coe v2) (coe v3)
                                        (coe v11)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                 v20))
                                           (coe v16)))
                                     (coe v12)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.insert
d_insert_920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_insert_920 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 v10
  = du_insert_920 v3 v5 v9 v10
du_insert_920 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny ->
  AgdaAny ->
  T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_insert_920 v0 v1 v2 v3
  = coe
      du_insertWith_818 (coe v0) (coe v1) (coe v2) (coe (\ v4 -> v3))
-- Data.Tree.AVL.Indexed._.delete
d_delete_936 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_delete_936 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_delete_936 v3 v6 v7 v8 v9 v10 v11
du_delete_936 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  AgdaAny ->
  T_Tree_180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_delete_936 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      C_leaf_192 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v5)
      C_node_208 v7 v8 v10 v11 v12 v13
        -> let v14 = subInt (coe v3) (coe (1 :: Integer)) in
           coe
             (case coe v10 of
                MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 v15 v16
                  -> case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                         -> let v19
                                  = coe
                                      MAlonzo.Code.Relation.Binary.Structures.d_compare_544
                                      (MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                                         (coe v0))
                                      v15 v4 in
                            coe
                              (case coe v19 of
                                 MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v20
                                   -> coe
                                        du_join'691''8315'_594 (coe v7) (coe v8) (coe v10) (coe v11)
                                        (coe
                                           du_delete_936 (coe v0)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                 (coe v15)))
                                           (coe v2) (coe v8) (coe v4) (coe v12)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                                 (coe
                                                    MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                    v20))
                                              (coe v18)))
                                        (coe v13)
                                 MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v21
                                   -> coe
                                        du_join_754 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v15)))
                                        (coe v2) (coe v7) (coe v8) (coe v14) (coe v11) (coe v12)
                                        (coe v13)
                                 MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v22
                                   -> coe
                                        du_join'737''8315'_532 (coe v7) (coe v8) (coe v10)
                                        (coe
                                           du_delete_936 (coe v0) (coe v1)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                 (coe v15)))
                                           (coe v7) (coe v4) (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                                 (coe
                                                    MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                                    v22))))
                                        (coe v12) (coe v13)
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.lookup
d_lookup_1034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  T_Tree_180 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Maybe AgdaAny
d_lookup_1034 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_lookup_1034 v3 v5 v9 v10 v11
du_lookup_1034 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  T_Tree_180 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Maybe AgdaAny
du_lookup_1034 v0 v1 v2 v3 v4
  = case coe v2 of
      C_leaf_192 v5 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_node_208 v5 v6 v8 v9 v10 v11
        -> case coe v8 of
             MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 v12 v13
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                      -> let v16
                               = coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_compare_544
                                   (MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
                                      (coe v0))
                                   v12 v3 in
                         coe
                           (case coe v16 of
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v17
                                -> coe
                                     du_lookup_1034 (coe v0) (coe v1) (coe v10) (coe v3)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                              v17))
                                        (coe v15))
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v18
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Data.Tree.AVL.Value.d_respects_48 v1 v12 v3 v18
                                        v13)
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v19
                                -> coe
                                     du_lookup_1034 (coe v0) (coe v1) (coe v9) (coe v3)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'91'_'93'_30
                                              v19)))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.foldr
d_foldr_1114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_Tree_180 -> AgdaAny
d_foldr_1114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
             v13
  = du_foldr_1114 v11 v12 v13
du_foldr_1114 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_Tree_180 -> AgdaAny
du_foldr_1114 v0 v1 v2
  = case coe v2 of
      C_leaf_192 v3 -> coe v1
      C_node_208 v3 v4 v6 v7 v8 v9
        -> case coe v6 of
             MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 v10 v11
               -> coe
                    du_foldr_1114 (coe v0)
                    (coe v0 v10 v11 (coe du_foldr_1114 (coe v0) (coe v1) (coe v8)))
                    (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.toDiffList
d_toDiffList_1140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  T_Tree_180 ->
  [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56] ->
  [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56]
d_toDiffList_1140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_toDiffList_1140 v9
du_toDiffList_1140 ::
  T_Tree_180 ->
  [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56] ->
  [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56]
du_toDiffList_1140 v0
  = case coe v0 of
      C_leaf_192 v1 -> coe (\ v2 -> v2)
      C_node_208 v1 v2 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Data.DifferenceList.du__'43''43'__38
             (coe du_toDiffList_1140 (coe v5))
             (coe
                MAlonzo.Code.Data.DifferenceList.du__'8759'__28 v4
                (coe du_toDiffList_1140 (coe v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Indexed._.toList
d_toList_1154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Integer ->
  T_Tree_180 -> [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56]
d_toList_1154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_toList_1154 v9
du_toList_1154 ::
  T_Tree_180 -> [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56]
du_toList_1154 v0
  = coe
      du_toDiffList_1140 v0
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Data.Tree.AVL.Indexed._.size
d_size_1164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) -> Integer -> T_Tree_180 -> Integer
d_size_1164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_size_1164
du_size_1164 :: T_Tree_180 -> Integer
du_size_1164
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe MAlonzo.Code.Data.List.Base.du_length_284)
      (coe du_toList_1154)
-- Data.Tree.AVL.Indexed._.Val
d_Val_1178 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Val_1178 = erased
-- Data.Tree.AVL.Indexed._.Wal
d_Wal_1180 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Wal_1180 = erased
-- Data.Tree.AVL.Indexed._.map
d_map_1188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) -> Integer -> T_Tree_180 -> T_Tree_180
d_map_1188 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 v12
  = du_map_1188 v8 v12
du_map_1188 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Tree_180 -> T_Tree_180
du_map_1188 v0 v1
  = case coe v1 of
      C_leaf_192 v2 -> coe v1
      C_node_208 v2 v3 v5 v6 v7 v8
        -> case coe v5 of
             MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 v9 v10
               -> coe
                    C_node_208 v2 v3
                    (coe
                       MAlonzo.Code.Data.Tree.AVL.Value.C__'44'__70 (coe v9)
                       (coe v0 v9 v10))
                    (coe du_map_1188 (coe v0) (coe v6))
                    (coe du_map_1188 (coe v0) (coe v7)) v8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
