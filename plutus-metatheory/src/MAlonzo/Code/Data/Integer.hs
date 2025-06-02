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

module MAlonzo.Code.Data.Integer where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.String qualified
import MAlonzo.Code.Data.Integer.Base qualified
import MAlonzo.Code.Data.Nat.Show qualified
import MAlonzo.Code.Data.Sign.Base qualified
import MAlonzo.Code.Data.String.Base qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Integer.show
d_show_4 :: Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show_4 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (coe
         du_showSign_12
         (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0)))
      (coe
         MAlonzo.Code.Data.Nat.Show.d_show_56
         (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
-- Data.Integer._.showSign
d_showSign_12 ::
  Integer ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showSign_12 ~v0 v1 = du_showSign_12 v1
du_showSign_12 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_showSign_12 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sign.Base.C_'45'_8  -> coe ("-" :: Data.Text.Text)
      MAlonzo.Code.Data.Sign.Base.C_'43'_10 -> coe ("" :: Data.Text.Text)
      _                                     -> MAlonzo.RTE.mazUnreachableError
