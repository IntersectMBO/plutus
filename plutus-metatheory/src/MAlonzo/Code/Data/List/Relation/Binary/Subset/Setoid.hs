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

module MAlonzo.Code.Data.List.Relation.Binary.Subset.Setoid where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.List.Relation.Binary.Subset.Setoid._⊆_
d__'8838'__44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8838'__44 = erased
-- Data.List.Relation.Binary.Subset.Setoid._⊇_
d__'8839'__52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8839'__52 = erased
-- Data.List.Relation.Binary.Subset.Setoid._⊈_
d__'8840'__54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8840'__54 = erased
-- Data.List.Relation.Binary.Subset.Setoid._⊉_
d__'8841'__60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8841'__60 = erased
