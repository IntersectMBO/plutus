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

module MAlonzo.Code.Data.Bool.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Primitive

-- Data.Bool.Base._≤_
d__'8804'__10 a0 a1 = ()
data T__'8804'__10 = C_f'8804't_12 | C_b'8804'b_16
-- Data.Bool.Base._<_
d__'60'__18 a0 a1 = ()
data T__'60'__18 = C_f'60't_20
-- Data.Bool.Base.not
d_not_22 :: Bool -> Bool
d_not_22 v0
  = if coe v0
      then coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      else coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
-- Data.Bool.Base._∧_
d__'8743'__24 :: Bool -> Bool -> Bool
d__'8743'__24 v0 v1 = if coe v0 then coe v1 else coe v0
-- Data.Bool.Base._∨_
d__'8744'__30 :: Bool -> Bool -> Bool
d__'8744'__30 v0 v1 = if coe v0 then coe v0 else coe v1
-- Data.Bool.Base._xor_
d__xor__36 :: Bool -> Bool -> Bool
d__xor__36 v0 v1 = if coe v0 then coe d_not_22 (coe v1) else coe v1
-- Data.Bool.Base.T
d_T_42 :: Bool -> ()
d_T_42 = erased
-- Data.Bool.Base.if_then_else_
d_if_then_else__44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Bool -> AgdaAny -> AgdaAny -> AgdaAny
d_if_then_else__44 ~v0 ~v1 v2 v3 v4 = du_if_then_else__44 v2 v3 v4
du_if_then_else__44 :: Bool -> AgdaAny -> AgdaAny -> AgdaAny
du_if_then_else__44 v0 v1 v2 = if coe v0 then coe v1 else coe v2
