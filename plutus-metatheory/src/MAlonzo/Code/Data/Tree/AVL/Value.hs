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

module MAlonzo.Code.Data.Tree.AVL.Value where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Tree.AVL.Value.Value
d_Value_38 a0 a1 a2 a3 = ()
newtype T_Value_38
  = C_MkValue_50 (AgdaAny ->
                  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Data.Tree.AVL.Value.Value.family
d_family_46 :: T_Value_38 -> AgdaAny -> ()
d_family_46 = erased
-- Data.Tree.AVL.Value.Value.respects
d_respects_48 ::
  T_Value_38 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_respects_48 v0
  = case coe v0 of
      C_MkValue_50 v2 -> coe v2
      _               -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Value.K&_
d_K'38'__56 a0 a1 a2 a3 a4 = ()
data T_K'38'__56 = C__'44'__70 AgdaAny AgdaAny
-- Data.Tree.AVL.Value.K&_.key
d_key_66 :: T_K'38'__56 -> AgdaAny
d_key_66 v0
  = case coe v0 of
      C__'44'__70 v1 v2 -> coe v1
      _                 -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Value.K&_.value
d_value_68 :: T_K'38'__56 -> AgdaAny
d_value_68 v0
  = case coe v0 of
      C__'44'__70 v1 v2 -> coe v2
      _                 -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Value._.toPair
d_toPair_80 ::
  T_K'38'__56 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_toPair_80 v0
  = case coe v0 of
      C__'44'__70 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Value._.fromPair
d_fromPair_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Value_38 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_K'38'__56
d_fromPair_86 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_fromPair_86 v5
du_fromPair_86 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_K'38'__56
du_fromPair_86 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe C__'44'__70 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Value.const
d_const_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_Value_38
d_const_94 ~v0 ~v1 ~v2 ~v3 ~v4 = du_const_94
du_const_94 :: T_Value_38
du_const_94
  = coe
      C_MkValue_50 (\ v0 v1 -> let v2 = \ v2 -> v2 in coe (\ v3 -> v2))
