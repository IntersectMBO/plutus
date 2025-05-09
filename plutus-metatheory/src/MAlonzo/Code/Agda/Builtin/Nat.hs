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

module MAlonzo.Code.Agda.Builtin.Nat where

import Data.Text qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Agda.Builtin.Nat.Nat
d_Nat_6 = ()
data T_Nat_6 = C_zero_8 | C_suc_12 Integer
-- Agda.Builtin.Nat._+_
d__'43'__14 = ((+) :: Integer -> Integer -> Integer)
-- Agda.Builtin.Nat._-_
d__'45'__22
  = ((\ x y -> max 0 (x - y)) :: Integer -> Integer -> Integer)
-- Agda.Builtin.Nat._*_
d__'42'__32 = ((*) :: Integer -> Integer -> Integer)
-- Agda.Builtin.Nat._==_
d__'61''61'__40 = ((==) :: Integer -> Integer -> Bool)
-- Agda.Builtin.Nat._<_
d__'60'__46 = ((<) :: Integer -> Integer -> Bool)
-- Agda.Builtin.Nat.div-helper
d_div'45'helper_60
  = ((\ k m n j -> k + div (max 0 $ n + m - j) (m + 1)) :: Integer -> Integer -> Integer -> Integer -> Integer)
-- Agda.Builtin.Nat.mod-helper
d_mod'45'helper_90
  = ((\ k m n j -> if n > j then mod (n - j - 1) (m + 1) else (k + n)) :: Integer -> Integer -> Integer -> Integer -> Integer)
