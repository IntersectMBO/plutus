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

module MAlonzo.Code.Data.Char.Base where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Char qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Char.Base._≈_
d__'8776'__6 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()
d__'8776'__6 = erased
-- Data.Char.Base._≉_
d__'8777'__8 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()
d__'8777'__8 = erased
-- Data.Char.Base._≈ᵇ_
d__'8776''7495'__14 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d__'8776''7495'__14 v0 v1
  = coe
      eqInt (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1)
-- Data.Char.Base._<_
d__'60'__20 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()
d__'60'__20 = erased
-- Data.Char.Base._≤_
d__'8804'__22 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()
d__'8804'__22 = erased
