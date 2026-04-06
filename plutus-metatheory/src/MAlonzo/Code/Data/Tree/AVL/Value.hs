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

module MAlonzo.Code.Data.Tree.AVL.Value where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Bundles

-- Data.Tree.AVL.Value.Value
d_Value_40 a0 a1 a2 a3 = ()
newtype T_Value_40
  = C_MkValue_52 (AgdaAny ->
                  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Data.Tree.AVL.Value.Value.family
d_family_48 :: T_Value_40 -> AgdaAny -> ()
d_family_48 = erased
-- Data.Tree.AVL.Value.Value.respects
d_respects_50 ::
  T_Value_40 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_respects_50 v0
  = case coe v0 of
      C_MkValue_52 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Value.K&_
d_K'38'__58 a0 a1 a2 a3 a4 = ()
data T_K'38'__58 = C__'44'__72 AgdaAny AgdaAny
-- Data.Tree.AVL.Value.K&_.key
d_key_68 :: T_K'38'__58 -> AgdaAny
d_key_68 v0
  = case coe v0 of
      C__'44'__72 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Value.K&_.value
d_value_70 :: T_K'38'__58 -> AgdaAny
d_value_70 v0
  = case coe v0 of
      C__'44'__72 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Value._.toPair
d_toPair_82 ::
  T_K'38'__58 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_toPair_82 v0
  = case coe v0 of
      C__'44'__72 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Value._.fromPair
d_fromPair_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Value_40 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_K'38'__58
d_fromPair_88 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_fromPair_88 v5
du_fromPair_88 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_K'38'__58
du_fromPair_88 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe C__'44'__72 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Value.const
d_const_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_Value_40
d_const_96 ~v0 ~v1 ~v2 ~v3 ~v4 = du_const_96
du_const_96 :: T_Value_40
du_const_96
  = coe
      C_MkValue_52 (\ v0 v1 -> let v2 = \ v2 -> v2 in coe (\ v3 -> v2))
