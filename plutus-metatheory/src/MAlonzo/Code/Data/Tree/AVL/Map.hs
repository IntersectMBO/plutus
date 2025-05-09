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

module MAlonzo.Code.Data.Tree.AVL.Map where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.List.Base qualified
import MAlonzo.Code.Data.Maybe.Base qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Data.Tree.AVL qualified
import MAlonzo.Code.Data.Tree.AVL.Indexed qualified
import MAlonzo.Code.Data.Tree.AVL.Value qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Tree.AVL.Map.AVL.Tree
d_Tree_42 a0 a1 a2 a3 a4 a5 = ()
-- Data.Tree.AVL.Map.Map
d_Map_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Map_194 = erased
-- Data.Tree.AVL.Map.empty
d_empty_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_empty_198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_empty_198
du_empty_198 :: MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_empty_198 = coe MAlonzo.Code.Data.Tree.AVL.du_empty_274
-- Data.Tree.AVL.Map.singleton
d_singleton_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_singleton_200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_singleton_200
du_singleton_200 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_singleton_200 = coe MAlonzo.Code.Data.Tree.AVL.du_singleton_278
-- Data.Tree.AVL.Map.insert
d_insert_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_insert_202 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_insert_202 v3
du_insert_202 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_insert_202 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_insert_286 (coe v0)
      (coe
         MAlonzo.Code.Data.Tree.AVL.Value.C_MkValue_50
         (\ v1 v2 -> let v3 = \ v3 -> v3 in coe (\ v4 -> v3)))
-- Data.Tree.AVL.Map.insertWith
d_insertWith_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_insertWith_204 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_insertWith_204 v3
du_insertWith_204 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_insertWith_204 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_insertWith_296 (coe v0)
      (coe
         MAlonzo.Code.Data.Tree.AVL.Value.C_MkValue_50
         (\ v1 v2 -> let v3 = \ v3 -> v3 in coe (\ v4 -> v3)))
-- Data.Tree.AVL.Map.delete
d_delete_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_delete_206 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_delete_206 v3
du_delete_206 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_delete_206 v0
  = coe MAlonzo.Code.Data.Tree.AVL.du_delete_304 (coe v0)
-- Data.Tree.AVL.Map.lookup
d_lookup_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> AgdaAny -> Maybe AgdaAny
d_lookup_208 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_lookup_208 v3
du_lookup_208 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> AgdaAny -> Maybe AgdaAny
du_lookup_208 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_lookup_312 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
-- Data.Tree.AVL.Map.map
d_map_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_map_210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_map_210 v8
du_map_210 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_map_210 v0
  = coe MAlonzo.Code.Data.Tree.AVL.du_map_334 (coe (\ v1 -> v0))
-- Data.Tree.AVL.Map.member
d_member_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> Bool
d_member_214 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_member_214 v3
du_member_214 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> Bool
du_member_214 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_member_350 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
-- Data.Tree.AVL.Map.headTail
d_headTail_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_headTail_216 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_headTail_216 v3
du_headTail_216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_headTail_216 v0
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Data.Maybe.Base.du_map_64
         (coe
            MAlonzo.Code.Data.Product.Base.du_map'8321'_138
            (coe MAlonzo.Code.Data.Tree.AVL.Value.d_toPair_80)))
      (coe MAlonzo.Code.Data.Tree.AVL.du_headTail_356 (coe v0))
-- Data.Tree.AVL.Map.initLast
d_initLast_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_initLast_218 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_initLast_218 v3
du_initLast_218 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_initLast_218 v0
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Data.Maybe.Base.du_map_64
         (coe
            MAlonzo.Code.Data.Product.Base.du_map'8322'_150
            (coe (\ v1 -> MAlonzo.Code.Data.Tree.AVL.Value.d_toPair_80))))
      (coe MAlonzo.Code.Data.Tree.AVL.du_initLast_368 (coe v0))
-- Data.Tree.AVL.Map.foldr
d_foldr_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> AgdaAny
d_foldr_220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_foldr_220 v8
du_foldr_220 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> AgdaAny
du_foldr_220 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_foldr_382 (coe (\ v1 -> coe v0 v1))
-- Data.Tree.AVL.Map.fromList
d_fromList_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_fromList_226 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_fromList_226 v3
du_fromList_226 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_fromList_226 v0
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Data.Tree.AVL.du_fromList_390 (coe v0)
         (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Data.Tree.AVL.Value.du_fromPair_86))
-- Data.Tree.AVL.Map.toList
d_toList_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_toList_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_toList_228
du_toList_228 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_toList_228
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Data.Tree.AVL.Value.d_toPair_80))
      (coe MAlonzo.Code.Data.Tree.AVL.du_toList_392)
-- Data.Tree.AVL.Map.size
d_size_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> Integer
d_size_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_size_230
du_size_230 :: MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> Integer
du_size_230 = coe MAlonzo.Code.Data.Tree.AVL.du_size_396
-- Data.Tree.AVL.Map.unionWith
d_unionWith_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_unionWith_232 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_unionWith_232 v3 v8
du_unionWith_232 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  (AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_unionWith_232 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_unionWith_418 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
      (coe (\ v2 -> v1))
-- Data.Tree.AVL.Map.union
d_union_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_union_236 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_union_236 v3
du_union_236 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_union_236 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_union_440 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
-- Data.Tree.AVL.Map.unionsWith
d_unionsWith_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_unionsWith_238 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_unionsWith_238 v3 v6
du_unionsWith_238 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  (AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_unionsWith_238 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_unionsWith_444 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
      (coe (\ v2 -> v1))
-- Data.Tree.AVL.Map.unions
d_unions_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_unions_242 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_unions_242 v3
du_unions_242 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_unions_242 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_unions_450 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
-- Data.Tree.AVL.Map.intersectionWith
d_intersectionWith_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_intersectionWith_244 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_intersectionWith_244 v3 v10
du_intersectionWith_244 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_intersectionWith_244 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_intersectionWith_476 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
      (coe (\ v2 -> v1))
-- Data.Tree.AVL.Map.intersection
d_intersection_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_intersection_248 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_intersection_248 v3
du_intersection_248 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_intersection_248 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_intersection_510 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
-- Data.Tree.AVL.Map.intersectionsWith
d_intersectionsWith_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_intersectionsWith_250 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_intersectionsWith_250 v3 v6
du_intersectionsWith_250 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_intersectionsWith_250 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_intersectionsWith_514 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
      (coe (\ v2 -> v1))
-- Data.Tree.AVL.Map.intersections
d_intersections_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
d_intersections_254 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_intersections_254 v3
du_intersections_254 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_254] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_254
du_intersections_254 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_intersections_524 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_94)
-- Data.Tree.AVL.Map._∈?_
d__'8712''63'__256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> Bool
d__'8712''63'__256 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du__'8712''63'__256 v3
du__'8712''63'__256 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_254 -> Bool
du__'8712''63'__256 v0 = coe du_member_214 (coe v0)
