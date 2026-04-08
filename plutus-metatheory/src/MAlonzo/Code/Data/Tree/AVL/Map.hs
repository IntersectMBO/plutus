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

module MAlonzo.Code.Data.Tree.AVL.Map where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Tree.AVL
import qualified MAlonzo.Code.Data.Tree.AVL.Indexed
import qualified MAlonzo.Code.Data.Tree.AVL.Value
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles

-- Data.Tree.AVL.Map.AVL.Tree
d_Tree_44 a0 a1 a2 a3 a4 a5 = ()
-- Data.Tree.AVL.Map.Map
d_Map_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Map_206 = erased
-- Data.Tree.AVL.Map.empty
d_empty_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_empty_210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_empty_210
du_empty_210 :: MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_empty_210 = coe MAlonzo.Code.Data.Tree.AVL.du_empty_286
-- Data.Tree.AVL.Map.singleton
d_singleton_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_singleton_212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_singleton_212
du_singleton_212 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_singleton_212 = coe MAlonzo.Code.Data.Tree.AVL.du_singleton_290
-- Data.Tree.AVL.Map.insert
d_insert_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_insert_214 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_insert_214 v3
du_insert_214 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_insert_214 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_insert_298 (coe v0)
      (coe
         MAlonzo.Code.Data.Tree.AVL.Value.C_MkValue_52
         (\ v1 v2 -> let v3 = \ v3 -> v3 in coe (\ v4 -> v3)))
-- Data.Tree.AVL.Map.insertWith
d_insertWith_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_insertWith_216 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_insertWith_216 v3
du_insertWith_216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  AgdaAny ->
  (Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_insertWith_216 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_insertWith_308 (coe v0)
      (coe
         MAlonzo.Code.Data.Tree.AVL.Value.C_MkValue_52
         (\ v1 v2 -> let v3 = \ v3 -> v3 in coe (\ v4 -> v3)))
-- Data.Tree.AVL.Map.delete
d_delete_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_delete_218 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_delete_218 v3
du_delete_218 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  AgdaAny ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_delete_218 v0
  = coe MAlonzo.Code.Data.Tree.AVL.du_delete_316 (coe v0)
-- Data.Tree.AVL.Map.lookup
d_lookup_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> AgdaAny -> Maybe AgdaAny
d_lookup_220 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_lookup_220 v3
du_lookup_220 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> AgdaAny -> Maybe AgdaAny
du_lookup_220 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_lookup_324 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96)
-- Data.Tree.AVL.Map.map
d_map_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_map_222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_map_222 v8
du_map_222 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_map_222 v0
  = coe MAlonzo.Code.Data.Tree.AVL.du_map_346 (coe (\ v1 -> v0))
-- Data.Tree.AVL.Map.member
d_member_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> Bool
d_member_226 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_member_226 v3
du_member_226 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> Bool
du_member_226 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_member_362 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96)
-- Data.Tree.AVL.Map.headTail
d_headTail_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_headTail_228 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_headTail_228 v3
du_headTail_228 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_headTail_228 v0
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Data.Maybe.Base.du_map_64
         (coe
            MAlonzo.Code.Data.Product.Base.du_map'8321'_138
            (coe MAlonzo.Code.Data.Tree.AVL.Value.d_toPair_82)))
      (coe MAlonzo.Code.Data.Tree.AVL.du_headTail_368 (coe v0))
-- Data.Tree.AVL.Map.initLast
d_initLast_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_initLast_230 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_initLast_230 v3
du_initLast_230 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_initLast_230 v0
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Data.Maybe.Base.du_map_64
         (coe
            MAlonzo.Code.Data.Product.Base.du_map'8322'_150
            (coe (\ v1 -> MAlonzo.Code.Data.Tree.AVL.Value.d_toPair_82))))
      (coe MAlonzo.Code.Data.Tree.AVL.du_initLast_380 (coe v0))
-- Data.Tree.AVL.Map.foldr
d_foldr_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> AgdaAny
d_foldr_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_foldr_232 v8
du_foldr_232 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> AgdaAny
du_foldr_232 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_foldr_394 (coe (\ v1 -> coe v0 v1))
-- Data.Tree.AVL.Map.fromList
d_fromList_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_fromList_238 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_fromList_238 v3
du_fromList_238 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_fromList_238 v0
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Data.Tree.AVL.du_fromList_402 (coe v0)
         (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Data.Tree.AVL.Value.du_fromPair_88))
-- Data.Tree.AVL.Map.toList
d_toList_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_toList_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_toList_240
du_toList_240 ::
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_toList_240
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Data.Tree.AVL.Value.d_toPair_82))
      (coe MAlonzo.Code.Data.Tree.AVL.du_toList_404)
-- Data.Tree.AVL.Map.size
d_size_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> Integer
d_size_242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_size_242
du_size_242 :: MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> Integer
du_size_242 = coe MAlonzo.Code.Data.Tree.AVL.du_size_408
-- Data.Tree.AVL.Map.unionWith
d_unionWith_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_unionWith_244 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_unionWith_244 v3 v8
du_unionWith_244 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  (AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_unionWith_244 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_unionWith_430 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96)
      (coe (\ v2 -> v1))
-- Data.Tree.AVL.Map.union
d_union_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_union_248 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_union_248 v3
du_union_248 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_union_248 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_union_452 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96)
-- Data.Tree.AVL.Map.unionsWith
d_unionsWith_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_unionsWith_250 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_unionsWith_250 v3 v6
du_unionsWith_250 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  (AgdaAny -> Maybe AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_unionsWith_250 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_unionsWith_456 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96)
      (coe (\ v2 -> v1))
-- Data.Tree.AVL.Map.unions
d_unions_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_unions_254 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_unions_254 v3
du_unions_254 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_unions_254 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_unions_462 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96)
-- Data.Tree.AVL.Map.intersectionWith
d_intersectionWith_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_intersectionWith_256 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_intersectionWith_256 v3 v10
du_intersectionWith_256 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_intersectionWith_256 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_intersectionWith_488 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96)
      (coe (\ v2 -> v1))
-- Data.Tree.AVL.Map.intersection
d_intersection_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_intersection_260 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_intersection_260 v3
du_intersection_260 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266 ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_intersection_260 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_intersection_522 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96)
-- Data.Tree.AVL.Map.intersectionsWith
d_intersectionsWith_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_intersectionsWith_262 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_intersectionsWith_262 v3 v6
du_intersectionsWith_262 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_intersectionsWith_262 v0 v1
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_intersectionsWith_526 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96)
      (coe (\ v2 -> v1))
-- Data.Tree.AVL.Map.intersections
d_intersections_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
d_intersections_266 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_intersections_266 v3
du_intersections_266 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  [MAlonzo.Code.Data.Tree.AVL.T_Tree_266] ->
  MAlonzo.Code.Data.Tree.AVL.T_Tree_266
du_intersections_266 v0
  = coe
      MAlonzo.Code.Data.Tree.AVL.du_intersections_536 (coe v0)
      (coe MAlonzo.Code.Data.Tree.AVL.Value.du_const_96)
-- Data.Tree.AVL.Map._∈?_
d__'8712''63'__268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> Bool
d__'8712''63'__268 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du__'8712''63'__268 v3
du__'8712''63'__268 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  AgdaAny -> MAlonzo.Code.Data.Tree.AVL.T_Tree_266 -> Bool
du__'8712''63'__268 v0 = coe du_member_226 (coe v0)
