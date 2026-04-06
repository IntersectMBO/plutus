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

module MAlonzo.Code.Data.Integer where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.Sign.Base
import qualified MAlonzo.Code.Data.String.Base

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
      MAlonzo.Code.Data.Sign.Base.C_'45'_8 -> coe ("-" :: Data.Text.Text)
      MAlonzo.Code.Data.Sign.Base.C_'43'_10 -> coe ("" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
