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

module MAlonzo.Code.Data.Vec.Functional where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Vec.Base

-- Data.Vec.Functional.Vector
d_Vector_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> Integer -> ()
d_Vector_22 = erased
-- Data.Vec.Functional.toVec
d_toVec_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_toVec_28 ~v0 ~v1 v2 = du_toVec_28 v2
du_toVec_28 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_toVec_28 v0
  = coe MAlonzo.Code.Data.Vec.Base.du_tabulate_452 (coe v0)
-- Data.Vec.Functional.fromVec
d_fromVec_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_fromVec_30 ~v0 ~v1 ~v2 = du_fromVec_30
du_fromVec_30 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_fromVec_30 = coe MAlonzo.Code.Data.Vec.Base.du_lookup_82
-- Data.Vec.Functional.toList
d_toList_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> [AgdaAny]
d_toList_32 ~v0 ~v1 v2 = du_toList_32 v2
du_toList_32 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> [AgdaAny]
du_toList_32 v0
  = coe MAlonzo.Code.Data.List.Base.du_tabulate_380 (coe v0)
-- Data.Vec.Functional.fromList
d_fromList_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_fromList_36 ~v0 ~v1 = du_fromList_36
du_fromList_36 ::
  [AgdaAny] -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_fromList_36 = coe MAlonzo.Code.Data.List.Base.du_lookup_390
-- Data.Vec.Functional.[]
d_'91''93'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_'91''93'_38 ~v0 ~v1 ~v2 = du_'91''93'_38
du_'91''93'_38 :: AgdaAny
du_'91''93'_38 = MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Functional._∷_
d__'8759'__40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d__'8759'__40 ~v0 ~v1 ~v2 v3 v4 v5 = du__'8759'__40 v3 v4 v5
du__'8759'__40 ::
  AgdaAny ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du__'8759'__40 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v0
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4 -> coe v1 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Functional.length
d_length_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> Integer
d_length_52 ~v0 ~v1 v2 ~v3 = du_length_52 v2
du_length_52 :: Integer -> Integer
du_length_52 v0 = coe v0
-- Data.Vec.Functional.head
d_head_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
d_head_56 ~v0 ~v1 ~v2 v3 = du_head_56 v3
du_head_56 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
du_head_56 v0 = coe v0 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
-- Data.Vec.Functional.tail
d_tail_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_tail_60 ~v0 ~v1 ~v2 v3 v4 = du_tail_60 v3 v4
du_tail_60 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_tail_60 v0 v1
  = coe v0 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v1)
-- Data.Vec.Functional.uncons
d_uncons_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_uncons_64 ~v0 ~v1 ~v2 v3 = du_uncons_64 v3
du_uncons_64 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_uncons_64 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_head_56 (coe v0)) (coe du_tail_60 (coe v0))
-- Data.Vec.Functional.replicate
d_replicate_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_replicate_70 ~v0 ~v1 ~v2 v3 ~v4 = du_replicate_70 v3
du_replicate_70 :: AgdaAny -> AgdaAny
du_replicate_70 v0 = coe v0
-- Data.Vec.Functional.insertAt
d_insertAt_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_insertAt_74 ~v0 ~v1 ~v2 v3 v4 v5 v6 = du_insertAt_74 v3 v4 v5 v6
du_insertAt_74 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_insertAt_74 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v3 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v2
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6 -> coe v0 v6
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe du_head_56 (coe v0)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    du_insertAt_74 (coe du_tail_60 (coe v0)) (coe v5) (coe v2) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Functional.removeAt
d_removeAt_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_removeAt_108 ~v0 ~v1 ~v2 v3 v4 v5 = du_removeAt_108 v3 v4 v5
du_removeAt_108 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_removeAt_108 v0 v1 v2
  = coe
      v0
      (coe MAlonzo.Code.Data.Fin.Base.du_punchIn_410 (coe v1) (coe v2))
-- Data.Vec.Functional.updateAt
d_updateAt_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_updateAt_114 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_updateAt_114 v3 v4 v5 v6
du_updateAt_114 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_updateAt_114 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v3 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe v2 (coe du_head_56 (coe v0))
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe v0 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe du_head_56 (coe v0)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    du_updateAt_114 (coe du_tail_60 (coe v0)) (coe v5) (coe v2)
                    (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Functional.map
d_map_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_map_150 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 = du_map_150 v4 v6 v7
du_map_150 ::
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_map_150 v0 v1 v2 = coe v0 (coe v1 v2)
-- Data.Vec.Functional._++_
d__'43''43'__156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d__'43''43'__156 ~v0 ~v1 v2 ~v3 v4 v5 v6
  = du__'43''43'__156 v2 v4 v5 v6
du__'43''43'__156 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du__'43''43'__156 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52 (coe v1) (coe v2)
      (coe MAlonzo.Code.Data.Fin.Base.du_splitAt_166 (coe v0) (coe v3))
-- Data.Vec.Functional.concat
d_concat_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_concat_166 ~v0 ~v1 v2 ~v3 v4 v5 = du_concat_166 v2 v4 v5
du_concat_166 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_concat_166 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Product.Base.du_uncurry_244
      (coe (\ v3 v4 -> coe v1 v4 v3))
      (coe MAlonzo.Code.Data.Fin.Base.du_quotRem_192 (coe v0) (coe v2))
-- Data.Vec.Functional.foldr
d_foldr_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
d_foldr_176 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_foldr_176 v4 v5 v6 v7
du_foldr_176 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
du_foldr_176 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v1
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                v0 (coe du_head_56 (coe v3))
                (coe
                   du_foldr_176 (coe v0) (coe v1) (coe v4) (coe du_tail_60 (coe v3))))
-- Data.Vec.Functional.foldl
d_foldl_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
d_foldl_194 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_foldl_194 v4 v5 v6 v7
du_foldl_194 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
du_foldl_194 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v1
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                du_foldl_194 (coe v0) (coe v0 v1 (coe du_head_56 (coe v3)))
                (coe v4) (coe du_tail_60 (coe v3)))
-- Data.Vec.Functional.rearrange
d_rearrange_210 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_rearrange_210 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_rearrange_210 v4 v5 v6
du_rearrange_210 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_rearrange_210 v0 v1 v2 = coe v1 (coe v0 v2)
-- Data.Vec.Functional._⊛_
d__'8859'__216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d__'8859'__216 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du__'8859'__216 v5 v6 v7
du__'8859'__216 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du__'8859'__216 v0 v1 v2 = coe v0 v2 (coe v1 v2)
-- Data.Vec.Functional._>>=_
d__'62''62''61'__218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d__'62''62''61'__218 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du__'62''62''61'__218 v5 v6 v7
du__'62''62''61'__218 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du__'62''62''61'__218 v0 v1 v2
  = coe du_concat_166 (coe v0) (coe du_map_150 (coe v2) (coe v1))
-- Data.Vec.Functional.zipWith
d_zipWith_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_zipWith_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 v10
  = du_zipWith_226 v6 v8 v9 v10
du_zipWith_226 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_zipWith_226 v0 v1 v2 v3 = coe v0 (coe v1 v3) (coe v2 v3)
-- Data.Vec.Functional.unzipWith
d_unzipWith_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzipWith_236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_unzipWith_236 v7 v8
du_unzipWith_236 ::
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzipWith_236 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v2 ->
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0 (coe v1 v2))))
      (coe
         (\ v2 ->
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0 (coe v1 v2))))
-- Data.Vec.Functional.zip
d_zip_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zip_242 ~v0 ~v1 ~v2 ~v3 ~v4 = du_zip_242
du_zip_242 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zip_242
  = coe
      du_zipWith_226 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
-- Data.Vec.Functional.unzip
d_unzip_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzip_244 ~v0 ~v1 ~v2 ~v3 ~v4 = du_unzip_244
du_unzip_244 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzip_244 = coe du_unzipWith_236 (coe (\ v0 -> v0))
-- Data.Vec.Functional.take
d_take_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_take_250 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_take_250 v4 v5
du_take_250 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_take_250 v0 v1 = coe v0 v1
-- Data.Vec.Functional.drop
d_drop_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_drop_262 ~v0 ~v1 v2 ~v3 v4 v5 = du_drop_262 v2 v4 v5
du_drop_262 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_drop_262 v0 v1 v2
  = coe
      v1
      (coe
         MAlonzo.Code.Data.Fin.Base.du__'8593''691'__84 (coe v0) (coe v2))
-- Data.Vec.Functional.reverse
d_reverse_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_reverse_270 ~v0 ~v1 v2 v3 v4 = du_reverse_270 v2 v3 v4
du_reverse_270 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_reverse_270 v0 v1 v2
  = coe
      v1 (MAlonzo.Code.Data.Fin.Base.d_opposite_384 (coe v0) (coe v2))
-- Data.Vec.Functional.init
d_init_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_init_274 ~v0 ~v1 ~v2 v3 v4 = du_init_274 v3 v4
du_init_274 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_init_274 v0 v1 = coe v0 v1
-- Data.Vec.Functional.last
d_last_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
d_last_278 ~v0 ~v1 v2 v3 = du_last_278 v2 v3
du_last_278 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
du_last_278 v0 v1
  = coe v1 (MAlonzo.Code.Data.Fin.Base.d_fromℕ_48 (coe v0))
-- Data.Vec.Functional.transpose
d_transpose_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_transpose_284 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_transpose_284 v4 v5 v6
du_transpose_284 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_transpose_284 v0 v1 v2 = coe v0 v2 v1
-- Data.Vec.Functional.remove
d_remove_286 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_remove_286 ~v0 ~v1 ~v2 v3 v4 = du_remove_286 v3 v4
du_remove_286 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_remove_286 v0 v1 = coe du_removeAt_108 (coe v1) (coe v0)
-- Data.Vec.Functional.insert
d_insert_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_insert_288 v0 v1 v2 v3 v4 v5 v6 = coe du_insertAt_74 v3 v4 v5 v6
