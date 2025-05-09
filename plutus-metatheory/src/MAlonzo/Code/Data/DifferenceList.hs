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

module MAlonzo.Code.Data.DifferenceList where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.List qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.List.Base qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.DifferenceList.DiffList
d_DiffList_12 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_DiffList_12 = erased
-- Data.DifferenceList.lift
d_lift_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ([AgdaAny] -> [AgdaAny]) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d_lift_16 ~v0 ~v1 v2 v3 v4 = du_lift_16 v2 v3 v4
du_lift_16 ::
  ([AgdaAny] -> [AgdaAny]) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du_lift_16 v0 v1 v2 = coe v0 (coe v1 v2)
-- Data.DifferenceList.[]
d_'91''93'_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny]
d_'91''93'_24 ~v0 ~v1 v2 = du_'91''93'_24 v2
du_'91''93'_24 :: [AgdaAny] -> [AgdaAny]
du_'91''93'_24 v0 = coe v0
-- Data.DifferenceList._∷_
d__'8759'__28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d__'8759'__28 ~v0 ~v1 v2 = du__'8759'__28 v2
du__'8759'__28 ::
  AgdaAny -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du__'8759'__28 v0
  = coe
      du_lift_16
      (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0))
-- Data.DifferenceList.[_]
d_'91'_'93'_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> [AgdaAny] -> [AgdaAny]
d_'91'_'93'_34 ~v0 ~v1 v2 = du_'91'_'93'_34 v2
du_'91'_'93'_34 :: AgdaAny -> [AgdaAny] -> [AgdaAny]
du_'91'_'93'_34 v0 = coe du__'8759'__28 v0 (\ v1 -> v1)
-- Data.DifferenceList._++_
d__'43''43'__38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ([AgdaAny] -> [AgdaAny]) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d__'43''43'__38 ~v0 ~v1 v2 v3 v4 = du__'43''43'__38 v2 v3 v4
du__'43''43'__38 ::
  ([AgdaAny] -> [AgdaAny]) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du__'43''43'__38 v0 v1 v2 = coe v0 (coe v1 v2)
-- Data.DifferenceList._∷ʳ_
d__'8759''691'__46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> ([AgdaAny] -> [AgdaAny]) -> AgdaAny -> [AgdaAny] -> [AgdaAny]
d__'8759''691'__46 ~v0 ~v1 v2 v3 v4 = du__'8759''691'__46 v2 v3 v4
du__'8759''691'__46 ::
  ([AgdaAny] -> [AgdaAny]) -> AgdaAny -> [AgdaAny] -> [AgdaAny]
du__'8759''691'__46 v0 v1 v2
  = coe
      v0
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2))
-- Data.DifferenceList.toList
d_toList_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny]
d_toList_54 ~v0 ~v1 v2 = du_toList_54 v2
du_toList_54 :: ([AgdaAny] -> [AgdaAny]) -> [AgdaAny]
du_toList_54 v0
  = coe v0 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Data.DifferenceList.fromList
d_fromList_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_fromList_58 ~v0 ~v1 v2 = du_fromList_58 v2
du_fromList_58 :: [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du_fromList_58 v0
  = coe
      MAlonzo.Code.Function.Base.du__'10216'_'10217'__240 (coe v0)
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
-- Data.DifferenceList.map
d_map_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d_map_64 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_map_64 v4 v5
du_map_64 ::
  (AgdaAny -> AgdaAny) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du_map_64 v0 v1
  = coe
      MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22 (coe v0)
         (coe du_toList_54 (coe v1)))
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
-- Data.DifferenceList.concat
d_concat_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ([[AgdaAny] -> [AgdaAny]] -> [[AgdaAny] -> [AgdaAny]]) ->
  [AgdaAny] -> [AgdaAny]
d_concat_72 ~v0 ~v1 v2 = du_concat_72 v2
du_concat_72 ::
  ([[AgdaAny] -> [AgdaAny]] -> [[AgdaAny] -> [AgdaAny]]) ->
  [AgdaAny] -> [AgdaAny]
du_concat_72 v0
  = coe du_concat'8242'_80 (coe du_toList_54 (coe v0))
-- Data.DifferenceList._.concat′
d_concat'8242'_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ([[AgdaAny] -> [AgdaAny]] -> [[AgdaAny] -> [AgdaAny]]) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [[AgdaAny] -> [AgdaAny]] -> [AgdaAny] -> [AgdaAny]
d_concat'8242'_80 ~v0 ~v1 ~v2 ~v3 ~v4 = du_concat'8242'_80
du_concat'8242'_80 ::
  [[AgdaAny] -> [AgdaAny]] -> [AgdaAny] -> [AgdaAny]
du_concat'8242'_80
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216 (coe du__'43''43'__38)
      (coe (\ v0 -> v0))
-- Data.DifferenceList.take
d_take_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d_take_82 ~v0 ~v1 v2 = du_take_82 v2
du_take_82 ::
  Integer -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du_take_82 v0
  = coe
      du_lift_16 (coe MAlonzo.Code.Data.List.Base.du_take_546 (coe v0))
-- Data.DifferenceList.drop
d_drop_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d_drop_86 ~v0 ~v1 v2 = du_drop_86 v2
du_drop_86 ::
  Integer -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du_drop_86 v0
  = coe
      du_lift_16 (coe MAlonzo.Code.Data.List.Base.du_drop_558 (coe v0))
