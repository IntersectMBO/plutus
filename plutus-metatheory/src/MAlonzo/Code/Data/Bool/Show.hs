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

module MAlonzo.Code.Data.Bool.Show where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.String

-- Data.Bool.Show.show
d_show_6 :: Bool -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show_6 v0
  = if coe v0
      then coe ("true" :: Data.Text.Text)
      else coe ("false" :: Data.Text.Text)
-- Data.Bool.Show.showBit
d_showBit_8 :: Bool -> MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_showBit_8 v0 = if coe v0 then coe '1' else coe '0'
