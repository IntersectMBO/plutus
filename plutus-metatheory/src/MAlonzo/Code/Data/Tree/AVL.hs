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

module MAlonzo.Code.Data.Tree.AVL where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.DifferenceList
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Tree.AVL.Height
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed
import qualified MAlonzo.Code.Data.Tree.AVL.Value
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict

-- Data.Tree.AVL.Indexed.K&_
d_K'38'__114 a0 a1 a2 a3 a4 a5 = ()
-- Data.Tree.AVL.Indexed.Tree
d_Tree_122 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Data.Tree.AVL.Indexed.Value
d_Value_124 a0 a1 a2 a3 a4 = ()
-- Data.Tree.AVL.Indexed.const
d_const_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40
d_const_132 ~v0 ~v1 ~v2 ~v3 = du_const_132
du_const_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40
du_const_132 v0 v1
  = coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96
-- Data.Tree.AVL.Indexed.fromPair
d_fromPair_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__58
d_fromPair_140 ~v0 ~v1 ~v2 ~v3 = du_fromPair_140
du_fromPair_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__58
du_fromPair_140 v0 v1 v2
  = coe MAlonzo.Code.Data.Tree.AVL.Value.du_fromPair_88 v2
-- Data.Tree.AVL.Indexed.toPair
d_toPair_194 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__58 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_toPair_194 = coe MAlonzo.Code.Data.Tree.AVL.Value.d_toPair_82
-- Data.Tree.AVL.Indexed.K&_.key
d_key_216 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__58 -> AgdaAny
d_key_216 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_key_68 (coe v0)
-- Data.Tree.AVL.Indexed.K&_.value
d_value_218 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__58 -> AgdaAny
d_value_218 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_value_70 (coe v0)
-- Data.Tree.AVL.Indexed.Value.family
d_family_228 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_family_228 = erased
-- Data.Tree.AVL.Indexed.Value.respects
d_respects_230 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_respects_230 v0
  = coe MAlonzo.Code.Data.Tree.AVL.Value.d_respects_50 (coe v0)
-- Data.Tree.AVL.Tree
d_Tree_266 a0 a1 a2 a3 a4 a5 = ()
data T_Tree_266
  = C_tree_274 Integer MAlonzo.Code.Data.Tree.AVL.Indexed.T_Tree_192
-- Data.Tree.AVL._.Val
d_Val_284 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_Val_284 = erased
-- Data.Tree.AVL._.empty
d_empty_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> T_Tree_266
d_empty_286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_empty_286
du_empty_286 :: T_Tree_266
du_empty_286
  = let v0 = coe C_tree_274 (coe (0 :: Integer)) in
    coe
      (coe
         v0
         (coe
            MAlonzo.Code.Data.Tree.AVL.Indexed.C_leaf_204
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30)))
-- Data.Tree.AVL._.singleton
d_singleton_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  AgdaAny -> AgdaAny -> T_Tree_266
d_singleton_290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_singleton_290 v6 v7
du_singleton_290 :: AgdaAny -> AgdaAny -> T_Tree_266
du_singleton_290 v0 v1
  = coe
      C_tree_274 (coe (1 :: Integer))
      (coe
         MAlonzo.Code.Data.Tree.AVL.Indexed.du_singleton_810 (coe v0)
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
d_insert_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  AgdaAny -> AgdaAny -> T_Tree_266 -> T_Tree_266
d_insert_298 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8
  = du_insert_298 v3 v5 v6 v7 v8
du_insert_298 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  AgdaAny -> AgdaAny -> T_Tree_266 -> T_Tree_266
du_insert_298 v0 v1 v2 v3 v4
  = case coe v4 of
      C_tree_274 v5 v6
        -> let v7
                 = coe
                     C_tree_274
                     (coe
                        MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Data.Tree.AVL.Indexed.du_insert_932 v0 v1 v2 v3 v6
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
                      MAlonzo.Code.Data.Tree.AVL.Indexed.du_insert_932 v0 v1 v2 v3 v6
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
d_insertWith_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  AgdaAny -> (Maybe AgdaAny -> AgdaAny) -> T_Tree_266 -> T_Tree_266
d_insertWith_308 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8
  = du_insertWith_308 v3 v5 v6 v7 v8
du_insertWith_308 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  AgdaAny -> (Maybe AgdaAny -> AgdaAny) -> T_Tree_266 -> T_Tree_266
du_insertWith_308 v0 v1 v2 v3 v4
  = case coe v4 of
      C_tree_274 v5 v6
        -> let v7
                 = coe
                     C_tree_274
                     (coe
                        MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_830 (coe v0)
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
                      MAlonzo.Code.Data.Tree.AVL.Indexed.du_insertWith_830 (coe v0)
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
d_delete_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  AgdaAny -> T_Tree_266 -> T_Tree_266
d_delete_316 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 = du_delete_316 v3 v6 v7
du_delete_316 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  AgdaAny -> T_Tree_266 -> T_Tree_266
du_delete_316 v0 v1 v2
  = case coe v2 of
      C_tree_274 v3 v4
        -> let v5
                 = coe
                     C_tree_274
                     (coe
                        MAlonzo.Code.Data.Tree.AVL.Height.d_pred'91'_'8853'_'93'_22
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              MAlonzo.Code.Data.Tree.AVL.Indexed.du_delete_948 (coe v0)
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
                      MAlonzo.Code.Data.Tree.AVL.Indexed.du_delete_948 (coe v0)
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
d_lookup_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  T_Tree_266 -> AgdaAny -> Maybe AgdaAny
d_lookup_324 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_lookup_324 v3 v5 v6 v7
du_lookup_324 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  T_Tree_266 -> AgdaAny -> Maybe AgdaAny
du_lookup_324 v0 v1 v2 v3
  = case coe v2 of
      C_tree_274 v4 v5
        -> coe
             MAlonzo.Code.Data.Tree.AVL.Indexed.du_lookup_1046 (coe v0) (coe v1)
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
d_Val_342 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_Val_342 = erased
-- Data.Tree.AVL._.Wal
d_Wal_344 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_Wal_344 = erased
-- Data.Tree.AVL._.map
d_map_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Tree_266 -> T_Tree_266
d_map_346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 = du_map_346 v8 v9
du_map_346 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Tree_266 -> T_Tree_266
du_map_346 v0 v1
  = case coe v1 of
      C_tree_274 v2 v3
        -> coe
             C_tree_274 (coe v2)
             (coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.du_map_1200 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.Val
d_Val_360 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_Val_360 = erased
-- Data.Tree.AVL._.member
d_member_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  AgdaAny -> T_Tree_266 -> Bool
d_member_362 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_member_362 v3 v5 v6 v7
du_member_362 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  AgdaAny -> T_Tree_266 -> Bool
du_member_362 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_is'45'just_20
      (coe du_lookup_324 (coe v0) (coe v1) (coe v3) (coe v2))
-- Data.Tree.AVL._.headTail
d_headTail_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  T_Tree_266 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_headTail_368 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 = du_headTail_368 v3 v6
du_headTail_368 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  T_Tree_266 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_headTail_368 v0 v1
  = case coe v1 of
      C_tree_274 v2 v3
        -> let v4
                 = let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                   coe
                     (let v5
                            = coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.du_headTail_660 (coe v4)
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
                                                      C_tree_274
                                                      (coe
                                                         MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                                                         (coe v10) (coe v4))
                                                      (coe
                                                         MAlonzo.Code.Data.Tree.AVL.Indexed.du_cast'737'_302
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
                                                                  MAlonzo.Code.Data.Tree.AVL.Value.d_key_68
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
                MAlonzo.Code.Data.Tree.AVL.Indexed.C_leaf_204 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.initLast
d_initLast_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  T_Tree_266 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_initLast_380 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 = du_initLast_380 v3 v6
du_initLast_380 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  T_Tree_266 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_initLast_380 v0 v1
  = case coe v1 of
      C_tree_274 v2 v3
        -> let v4
                 = let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                   coe
                     (let v5
                            = coe
                                MAlonzo.Code.Data.Tree.AVL.Indexed.du_initLast_710 (coe v4)
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
                                                      C_tree_274
                                                      (coe
                                                         MAlonzo.Code.Data.Tree.AVL.Height.d__'8853'__16
                                                         (coe v10) (coe v4))
                                                      (coe
                                                         MAlonzo.Code.Data.Tree.AVL.Indexed.du_cast'691'_328
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
                                                                  MAlonzo.Code.Data.Tree.AVL.Value.d_key_68
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
                MAlonzo.Code.Data.Tree.AVL.Indexed.C_leaf_204 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.foldr
d_foldr_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_Tree_266 -> AgdaAny
d_foldr_394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_foldr_394 v8 v9 v10
du_foldr_394 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_Tree_266 -> AgdaAny
du_foldr_394 v0 v1 v2
  = case coe v2 of
      C_tree_274 v3 v4
        -> coe
             MAlonzo.Code.Data.Tree.AVL.Indexed.du_foldr_1126 (coe v0) (coe v1)
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.fromList
d_fromList_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__58] -> T_Tree_266
d_fromList_402 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_fromList_402 v3 v5
du_fromList_402 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__58] -> T_Tree_266
du_fromList_402 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216
         (coe
            MAlonzo.Code.Data.Product.Base.du_uncurry_244
            (coe du_insert_298 (coe v0) (coe v1)))
         (coe MAlonzo.Code.Data.Tree.AVL.Value.d_toPair_82))
      (coe du_empty_286)
-- Data.Tree.AVL._.toList
d_toList_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  T_Tree_266 -> [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__58]
d_toList_404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_toList_404 v6
du_toList_404 ::
  T_Tree_266 -> [MAlonzo.Code.Data.Tree.AVL.Value.T_K'38'__58]
du_toList_404 v0
  = case coe v0 of
      C_tree_274 v1 v2
        -> coe
             MAlonzo.Code.Data.DifferenceList.du_toList_54
             (coe
                MAlonzo.Code.Data.Tree.AVL.Indexed.du_toDiffList_1152 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.size
d_size_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  T_Tree_266 -> Integer
d_size_408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_size_408 v6
du_size_408 :: T_Tree_266 -> Integer
du_size_408 v0
  = case coe v0 of
      C_tree_274 v1 v2
        -> coe MAlonzo.Code.Data.Tree.AVL.Indexed.du_size_1176 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.Val
d_Val_424 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_Val_424 = erased
-- Data.Tree.AVL._.Wal
d_Wal_426 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_Wal_426 = erased
-- Data.Tree.AVL._.unionWith
d_unionWith_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  T_Tree_266 -> T_Tree_266 -> T_Tree_266
d_unionWith_430 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_unionWith_430 v3 v7 v8 v9 v10
du_unionWith_430 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  T_Tree_266 -> T_Tree_266 -> T_Tree_266
du_unionWith_430 v0 v1 v2 v3 v4
  = coe
      du_foldr_394
      (coe
         (\ v5 v6 ->
            coe du_insertWith_308 (coe v0) (coe v1) (coe v5) (coe v2 v5 v6)))
      (coe v4) (coe v3)
-- Data.Tree.AVL._.Val
d_Val_450 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_Val_450 = erased
-- Data.Tree.AVL._.union
d_union_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  T_Tree_266 -> T_Tree_266 -> T_Tree_266
d_union_452 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_union_452 v3 v5
du_union_452 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  T_Tree_266 -> T_Tree_266 -> T_Tree_266
du_union_452 v0 v1
  = coe du_unionWith_430 (coe v0) (coe v1) (coe (\ v2 v3 v4 -> v3))
-- Data.Tree.AVL._.unionsWith
d_unionsWith_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  [T_Tree_266] -> T_Tree_266
d_unionsWith_456 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_unionsWith_456 v3 v5 v6 v7
du_unionsWith_456 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  [T_Tree_266] -> T_Tree_266
du_unionsWith_456 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe du_unionWith_430 (coe v0) (coe v1) (coe v2))
      (coe du_empty_286) (coe v3)
-- Data.Tree.AVL._.unions
d_unions_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  [T_Tree_266] -> T_Tree_266
d_unions_462 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_unions_462 v3 v5
du_unions_462 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  [T_Tree_266] -> T_Tree_266
du_unions_462 v0 v1
  = coe du_unionsWith_456 (coe v0) (coe v1) (coe (\ v2 v3 v4 -> v3))
-- Data.Tree.AVL._.Val
d_Val_480 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_Val_480 = erased
-- Data.Tree.AVL._.Wal
d_Wal_482 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_Wal_482 = erased
-- Data.Tree.AVL._.Xal
d_Xal_484 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_Xal_484 = erased
-- Data.Tree.AVL._.intersectionWith
d_intersectionWith_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Tree_266 -> T_Tree_266 -> T_Tree_266
d_intersectionWith_488 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
                       v12
  = du_intersectionWith_488 v3 v8 v9 v10 v11 v12
du_intersectionWith_488 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Tree_266 -> T_Tree_266 -> T_Tree_266
du_intersectionWith_488 v0 v1 v2 v3 v4 v5
  = coe
      du_foldr_394
      (coe du_cons_502 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
      (coe du_empty_286) (coe v4)
-- Data.Tree.AVL._._.cons
d_cons_502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Tree_266 ->
  T_Tree_266 -> AgdaAny -> AgdaAny -> T_Tree_266 -> T_Tree_266
d_cons_502 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11 v12 v13
           v14
  = du_cons_502 v3 v8 v9 v10 v12 v13 v14
du_cons_502 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Tree_266 -> AgdaAny -> AgdaAny -> T_Tree_266 -> T_Tree_266
du_cons_502 v0 v1 v2 v3 v4 v5 v6
  = let v7 = coe du_lookup_324 (coe v0) (coe v1) (coe v4) (coe v5) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
           -> coe du_insert_298 (coe v0) (coe v2) (coe v5) (coe v3 v5 v6 v8)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (\ v8 -> v8)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Tree.AVL._.Val
d_Val_520 ::
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 -> AgdaAny -> ()
d_Val_520 = erased
-- Data.Tree.AVL._.intersection
d_intersection_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  T_Tree_266 -> T_Tree_266 -> T_Tree_266
d_intersection_522 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_intersection_522 v3 v5
du_intersection_522 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  T_Tree_266 -> T_Tree_266 -> T_Tree_266
du_intersection_522 v0 v1
  = coe
      du_intersectionWith_488 (coe v0) (coe v1) (coe v1)
      (coe (\ v2 v3 v4 -> v3))
-- Data.Tree.AVL._.intersectionsWith
d_intersectionsWith_526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [T_Tree_266] -> T_Tree_266
d_intersectionsWith_526 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_intersectionsWith_526 v3 v5 v6 v7
du_intersectionsWith_526 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [T_Tree_266] -> T_Tree_266
du_intersectionsWith_526 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe du_empty_286
      (:) v4 v5
        -> coe
             MAlonzo.Code.Data.List.Base.du_foldl_230
             (coe du_intersectionWith_488 (coe v0) (coe v1) (coe v1) (coe v2))
             (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL._.intersections
d_intersections_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  [T_Tree_266] -> T_Tree_266
d_intersections_536 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_intersections_536 v3 v5
du_intersections_536 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  [T_Tree_266] -> T_Tree_266
du_intersections_536 v0 v1
  = coe
      du_intersectionsWith_526 (coe v0) (coe v1) (coe (\ v2 v3 v4 -> v3))
-- Data.Tree.AVL._∈?_
d__'8712''63'__542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  AgdaAny -> T_Tree_266 -> Bool
d__'8712''63'__542 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du__'8712''63'__542 v3 v5
du__'8712''63'__542 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.Value.T_Value_40 ->
  AgdaAny -> T_Tree_266 -> Bool
du__'8712''63'__542 v0 v1 = coe du_member_362 (coe v0) (coe v1)
