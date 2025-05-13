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

module MAlonzo.Code.Data.Tree.AVL where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.DifferenceList qualified
import MAlonzo.Code.Data.List.Base qualified
import MAlonzo.Code.Data.Maybe.Base qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Data.Tree.AVL.Height qualified
import MAlonzo.Code.Data.Tree.AVL.Indexed qualified
import MAlonzo.Code.Data.Tree.AVL.Value qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Tree.AVL.Indexed.K&_
d_K'38'__106 a0 a1 a2 a3 a4 a5 = ()
-- Data.Tree.AVL.Indexed.Tree
d_Tree_112 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Data.Tree.AVL.Indexed.Value
d_Value_114 a0 a1 a2 a3 a4 = ()
-- Data.Tree.AVL.Indexed.const
d_const_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38
d_const_120 ~v0 ~v1 ~v2 ~v3 = du_const_120
du_const_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38
du_const_120 v0 v1
  = coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94
-- Data.Tree.AVL.Indexed.fromPair
d_fromPair_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56
d_fromPair_128 ~v0 ~v1 ~v2 ~v3 = du_fromPair_128
du_fromPair_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56
du_fromPair_128 v0 v1 v2
  = coe MAlonzo.Code.Data.Tree.AVL.Value.du_fromPair_86 v2
-- Data.Tree.AVL.Indexed.toPair
d_toPair_182 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_toPair_182 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v0))
      (coe MAlonzo.Code.Data.Tree.AVL.Value.d_value_68 (coe v0))
-- Data.Tree.AVL.Indexed.K&_.key
d_key_204 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> AgdaAny
d_key_204 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_66 (coe v0)
-- Data.Tree.AVL.Indexed.K&_.value
d_value_206 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56 -> AgdaAny
d_value_206 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_value_68 (coe v0)
-- Data.Tree.AVL.Indexed.Value.family
d_family_216 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_family_216 = erased
-- Data.Tree.AVL.Indexed.Value.respects
d_respects_218 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_respects_218 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_respects_48 (coe v0)
-- Data.Tree.AVL.Tree
d_Tree_254 a0 a1 a2 a3 a4 a5 = ()
data T_Tree_254
  = C_tree_262 Integer MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_180
-- Data.Tree.AVL._.Val
d_Val_272 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Val_272 = erased
-- Data.Tree.AVL._.empty
d_empty_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> T_Tree_254
d_empty_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_empty_274
du_empty_274 :: T_Tree_254
du_empty_274
  = let v0 = coe C_tree_262 (coe (0 :: Integer)) in
    coe
      (coe
         v0
         (coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.C_leaf_192
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30)))
-- Data.Tree.AVL._.singleton
d_singleton_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> AgdaAny -> T_Tree_254
d_singleton_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_singleton_278 v6 v7
du_singleton_278 :: AgdaAny -> AgdaAny -> T_Tree_254
du_singleton_278 v0 v1
  = coe
      C_tree_262 (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Tree.AVL.Indexed.du_singleton_798 (coe v0)
         (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30)))
-- Data.Tree.AVL._.insert
d_insert_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> AgdaAny -> T_Tree_254 -> T_Tree_254
d_insert_286 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8
  = du_insert_286 v3 v5 v6 v7 v8
du_insert_286 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> AgdaAny -> T_Tree_254 -> T_Tree_254
du_insert_286 v0 v1 v2 v3 v4
  = case coe v4 of
      C_tree_262 v5 v6
        -> let v7
                 = coe
                     C_tree_262
                     (coe
                        MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Data.Tree.AVL.Indexed.du_insert_920 v0 v1 v2 v3 v6
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30))))
                        (coe v5)) in
           coe
             (coe
                v7
                (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Data.Tree.AVL.Indexed.du_insert_920 v0 v1 v2 v3 v6
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                            (coe
                               MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
                         (coe
                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.insertWith
d_insertWith_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> (Maybe AgdaAny -> AgdaAny) -> T_Tree_254 -> T_Tree_254
d_insertWith_296 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8
  = du_insertWith_296 v3 v5 v6 v7 v8
du_insertWith_296 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> (Maybe AgdaAny -> AgdaAny) -> T_Tree_254 -> T_Tree_254
du_insertWith_296 v0 v1 v2 v3 v4
  = case coe v4 of
      C_tree_262 v5 v6
        -> let v7
                 = coe
                     C_tree_262
                     (coe
                        MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818 (coe v0)
                              (coe v1) (coe v2) (coe v3) (coe v6)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30))))
                        (coe v5)) in
           coe
             (coe
                v7
                (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_818 (coe v0)
                      (coe v1) (coe v2) (coe v3) (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                            (coe
                               MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
                         (coe
                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.delete
d_delete_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> T_Tree_254 -> T_Tree_254
d_delete_304 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 = du_delete_304 v3 v6 v7
du_delete_304 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny -> T_Tree_254 -> T_Tree_254
du_delete_304 v0 v1 v2
  = case coe v2 of
      C_tree_262 v3 v4
        -> let v5
                 = coe
                     C_tree_262
                     (coe
                        MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Data.Tree.AVL.Indexed.du_delete_936 (coe v0)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v3)
                              (coe v1) (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30))))
                        (coe v3)) in
           coe
             (coe
                v5
                (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Data.Tree.AVL.Indexed.du_delete_936 (coe v0)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v3)
                      (coe v1) (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                            (coe
                               MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
                         (coe
                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.lookup
d_lookup_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  T_Tree_254 -> AgdaAny -> Maybe AgdaAny
d_lookup_312 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_lookup_312 v3 v5 v6 v7
du_lookup_312 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  T_Tree_254 -> AgdaAny -> Maybe AgdaAny
du_lookup_312 v0 v1 v2 v3
  = case coe v2 of
      C_tree_262 v4 v5
        -> coe
             MAlonzo.Code.Data.Tree.AVL.Indexed.du_lookup_1034 (coe v0) (coe v1)
             (coe v5) (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                   (coe
                      MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
                (coe
                   MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.Val
d_Val_330 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Val_330 = erased
-- Data.Tree.AVL._.Wal
d_Wal_332 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Wal_332 = erased
-- Data.Tree.AVL._.map
d_map_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Tree_254 -> T_Tree_254
d_map_334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 = du_map_334 v8 v9
du_map_334 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Tree_254 -> T_Tree_254
du_map_334 v0 v1
  = case coe v1 of
      C_tree_262 v2 v3
        -> coe
             C_tree_262 (coe v2)
             (coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.du_map_1188 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.Val
d_Val_348 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Val_348 = erased
-- Data.Tree.AVL._.member
d_member_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> T_Tree_254 -> Bool
d_member_350 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_member_350 v3 v5 v6 v7
du_member_350 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> T_Tree_254 -> Bool
du_member_350 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_is'45'just_20
      (coe du_lookup_312 (coe v0) (coe v1) (coe v3) (coe v2))
-- Data.Tree.AVL._.headTail
d_headTail_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  T_Tree_254 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_headTail_356 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 = du_headTail_356 v3 v6
du_headTail_356 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  T_Tree_254 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_headTail_356 v0 v1
  = case coe v1 of
      C_tree_262 v2 v3
        -> let v4
                 = let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                   coe
                     (let v5
                            = coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.du_headTail_648 (coe v4)
                                (coe v3) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                             -> case coe v7 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                    -> case coe v9 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v6)
                                                   (coe
                                                      C_tree_262
                                                      (coe
                                                         MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                                                         (coe v10) (coe v4))
                                                      (coe
                                                         MAlonzo.Code.Data.Tree.AVL.Indexed.du_cast'737'_290
                                                         (coe v0)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                               (coe
                                                                  MAlonzo.Code.Data.Tree.AVL.Value.d_key_66
                                                                  (coe v6))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                         (coe
                                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
                                                            (coe
                                                               MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
                                                         (coe v11))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Data.Tree.AVL.Indexed.C_leaf_192 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.initLast
d_initLast_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  T_Tree_254 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_initLast_368 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 = du_initLast_368 v3 v6
du_initLast_368 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  T_Tree_254 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_initLast_368 v0 v1
  = case coe v1 of
      C_tree_262 v2 v3
        -> let v4
                 = let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                   coe
                     (let v5
                            = coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.du_initLast_698 (coe v4)
                                (coe v3) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                             -> case coe v7 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                    -> case coe v9 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      C_tree_262
                                                      (coe
                                                         MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                                                         (coe v10) (coe v4))
                                                      (coe
                                                         MAlonzo.Code.Data.Tree.AVL.Indexed.du_cast'691'_316
                                                         (coe v0)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                               (coe
                                                                  MAlonzo.Code.Data.Tree.AVL.Value.d_key_66
                                                                  (coe v6))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                         (coe v11)
                                                         (coe
                                                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30)))
                                                   (coe v6))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Data.Tree.AVL.Indexed.C_leaf_192 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.foldr
d_foldr_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_Tree_254 -> AgdaAny
d_foldr_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_foldr_382 v8 v9 v10
du_foldr_382 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_Tree_254 -> AgdaAny
du_foldr_382 v0 v1 v2
  = case coe v2 of
      C_tree_262 v3 v4
        -> coe
             MAlonzo.Code.Data.Tree.AVL.Indexed.du_foldr_1114 (coe v0) (coe v1)
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.fromList
d_fromList_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56] -> T_Tree_254
d_fromList_390 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_fromList_390 v3 v5
du_fromList_390 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56] -> T_Tree_254
du_fromList_390 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216
         (coe
            MAlonzo.Code.Data.Product.Base.du_uncurry_244
            (coe du_insert_286 (coe v0) (coe v1)))
         (coe MAlonzo.Code.Data.Tree.AVL.Value.d_toPair_80))
      (coe du_empty_274)
-- Data.Tree.AVL._.toList
d_toList_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  T_Tree_254 -> [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56]
d_toList_392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_toList_392 v6
du_toList_392 ::
  T_Tree_254 -> [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__56]
du_toList_392 v0
  = case coe v0 of
      C_tree_262 v1 v2
        -> coe
             MAlonzo.Code.Data.DifferenceList.du_toList_54
             (coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.du_toDiffList_1140 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.size
d_size_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  T_Tree_254 -> Integer
d_size_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_size_396 v6
du_size_396 :: T_Tree_254 -> Integer
du_size_396 v0
  = case coe v0 of
      C_tree_262 v1 v2
        -> coe MAlonzo.Code.Data.Tree.AVL.Indexed.du_size_1164 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.Val
d_Val_412 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Val_412 = erased
-- Data.Tree.AVL._.Wal
d_Wal_414 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Wal_414 = erased
-- Data.Tree.AVL._.unionWith
d_unionWith_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  T_Tree_254 -> T_Tree_254 -> T_Tree_254
d_unionWith_418 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_unionWith_418 v3 v7 v8 v9 v10
du_unionWith_418 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  T_Tree_254 -> T_Tree_254 -> T_Tree_254
du_unionWith_418 v0 v1 v2 v3 v4
  = coe
      du_foldr_382
      (coe
         (\ v5 v6 ->
            coe du_insertWith_296 (coe v0) (coe v1) (coe v5) (coe v2 v5 v6)))
      (coe v4) (coe v3)
-- Data.Tree.AVL._.Val
d_Val_438 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Val_438 = erased
-- Data.Tree.AVL._.union
d_union_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  T_Tree_254 -> T_Tree_254 -> T_Tree_254
d_union_440 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_union_440 v3 v5
du_union_440 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  T_Tree_254 -> T_Tree_254 -> T_Tree_254
du_union_440 v0 v1
  = coe du_unionWith_418 (coe v0) (coe v1) (coe (\ v2 v3 v4 -> v3))
-- Data.Tree.AVL._.unionsWith
d_unionsWith_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  [T_Tree_254] -> T_Tree_254
d_unionsWith_444 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_unionsWith_444 v3 v5 v6 v7
du_unionsWith_444 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  [T_Tree_254] -> T_Tree_254
du_unionsWith_444 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe du_unionWith_418 (coe v0) (coe v1) (coe v2))
      (coe du_empty_274) (coe v3)
-- Data.Tree.AVL._.unions
d_unions_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  [T_Tree_254] -> T_Tree_254
d_unions_450 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_unions_450 v3 v5
du_unions_450 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  [T_Tree_254] -> T_Tree_254
du_unions_450 v0 v1
  = coe du_unionsWith_444 (coe v0) (coe v1) (coe (\ v2 v3 v4 -> v3))
-- Data.Tree.AVL._.Val
d_Val_468 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Val_468 = erased
-- Data.Tree.AVL._.Wal
d_Wal_470 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Wal_470 = erased
-- Data.Tree.AVL._.Xal
d_Xal_472 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Xal_472 = erased
-- Data.Tree.AVL._.intersectionWith
d_intersectionWith_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Tree_254 -> T_Tree_254 -> T_Tree_254
d_intersectionWith_476 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
                       v12
  = du_intersectionWith_476 v3 v8 v9 v10 v11 v12
du_intersectionWith_476 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Tree_254 -> T_Tree_254 -> T_Tree_254
du_intersectionWith_476 v0 v1 v2 v3 v4 v5
  = coe
      du_foldr_382
      (coe du_cons_490 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
      (coe du_empty_274) (coe v4)
-- Data.Tree.AVL._._.cons
d_cons_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Tree_254 ->
  T_Tree_254 -> AgdaAny -> AgdaAny -> T_Tree_254 -> T_Tree_254
d_cons_490 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11 v12 v13
           v14
  = du_cons_490 v3 v8 v9 v10 v12 v13 v14
du_cons_490 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Tree_254 -> AgdaAny -> AgdaAny -> T_Tree_254 -> T_Tree_254
du_cons_490 v0 v1 v2 v3 v4 v5 v6
  = let v7 = coe du_lookup_312 (coe v0) (coe v1) (coe v4) (coe v5) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
           -> coe
                du_insert_286 (coe v0)
                (coe
                   MAlonzo.Code.Data.Tree.AVL.Value.C_MkValue_50
                   (MAlonzo.Code.Data.Tree.AVL.Value.d_respects_48 (coe v2)))
                (coe v5) (coe v3 v5 v6 v8)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (\ v8 -> v8)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Tree.AVL._.Val
d_Val_508 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 -> AgdaAny -> ()
d_Val_508 = erased
-- Data.Tree.AVL._.intersection
d_intersection_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  T_Tree_254 -> T_Tree_254 -> T_Tree_254
d_intersection_510 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_intersection_510 v3 v5
du_intersection_510 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  T_Tree_254 -> T_Tree_254 -> T_Tree_254
du_intersection_510 v0 v1
  = coe
      du_intersectionWith_476 (coe v0) (coe v1) (coe v1)
      (coe (\ v2 v3 v4 -> v3))
-- Data.Tree.AVL._.intersectionsWith
d_intersectionsWith_514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [T_Tree_254] -> T_Tree_254
d_intersectionsWith_514 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_intersectionsWith_514 v3 v5 v6 v7
du_intersectionsWith_514 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [T_Tree_254] -> T_Tree_254
du_intersectionsWith_514 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe du_empty_274
      (:) v4 v5
        -> coe
             MAlonzo.Code.Data.List.Base.du_foldl_230
             (coe du_intersectionWith_476 (coe v0) (coe v1) (coe v1) (coe v2))
             (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.intersections
d_intersections_524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  [T_Tree_254] -> T_Tree_254
d_intersections_524 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_intersections_524 v3 v5
du_intersections_524 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  [T_Tree_254] -> T_Tree_254
du_intersections_524 v0 v1
  = coe
      du_intersectionsWith_514 (coe v0) (coe v1) (coe (\ v2 v3 v4 -> v3))
-- Data.Tree.AVL._∈?_
d__'8712''63'__530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> T_Tree_254 -> Bool
d__'8712''63'__530 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du__'8712''63'__530 v3 v5
du__'8712''63'__530 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_38 ->
  AgdaAny -> T_Tree_254 -> Bool
du__'8712''63'__530 v0 v1 = coe du_member_350 (coe v0) (coe v1)
