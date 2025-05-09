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

module MAlonzo.Code.Data.Float.Base where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Float qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Float.Base._≈_
d__'8776'__6 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 -> ()
d__'8776'__6 = erased
-- Data.Float.Base._≤_
d__'8804'__8 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 -> ()
d__'8804'__8 = erased
-- Data.Float.Base.toWord
d_toWord_14 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  Maybe MAlonzo.RTE.Word64
d_toWord_14
  = coe MAlonzo.Code.Agda.Builtin.Float.d_primFloatToWord64_22
