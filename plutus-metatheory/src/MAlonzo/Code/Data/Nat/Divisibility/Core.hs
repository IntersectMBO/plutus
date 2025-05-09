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

module MAlonzo.Code.Data.Nat.Divisibility.Core where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Data.Nat.Base qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Nat.Divisibility.Core._∣_
d__'8739'__20 a0 a1 = ()
newtype T__'8739'__20 = C_divides_34 Integer
-- Data.Nat.Divisibility.Core._∣_.quotient
d_quotient_30 :: T__'8739'__20 -> Integer
d_quotient_30 v0
  = case coe v0 of
      C_divides_34 v1 -> coe v1
      _               -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.Core._∣_.equality
d_equality_32 ::
  T__'8739'__20 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_equality_32 = erased
-- Data.Nat.Divisibility.Core._∤_
d__'8740'__36 :: Integer -> Integer -> ()
d__'8740'__36 = erased
-- Data.Nat.Divisibility.Core._HasNonTrivialDivisorLessThan_
d__HasNonTrivialDivisorLessThan__50 a0 a1 = ()
data T__HasNonTrivialDivisorLessThan__50
  = C_hasNonTrivialDivisor_72 Integer
                              MAlonzo.Code.Data.Nat.Base.T__'8804'__22 T__'8739'__20
-- Data.Nat.Divisibility.Core._HasNonTrivialDivisorLessThan_.divisor
d_divisor_64 :: T__HasNonTrivialDivisorLessThan__50 -> Integer
d_divisor_64 v0
  = case coe v0 of
      C_hasNonTrivialDivisor_72 v1 v3 v4 -> coe v1
      _                                  -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.Core._HasNonTrivialDivisorLessThan_.divisor-<
d_divisor'45''60'_68 ::
  T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_divisor'45''60'_68 v0
  = case coe v0 of
      C_hasNonTrivialDivisor_72 v1 v3 v4 -> coe v3
      _                                  -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.Core._HasNonTrivialDivisorLessThan_.divisor-∣
d_divisor'45''8739'_70 ::
  T__HasNonTrivialDivisorLessThan__50 -> T__'8739'__20
d_divisor'45''8739'_70 v0
  = case coe v0 of
      C_hasNonTrivialDivisor_72 v1 v3 v4 -> coe v4
      _                                  -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.Core.*-pres-∣
d_'42''45'pres'45''8739'_74 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> T__'8739'__20 -> T__'8739'__20 -> T__'8739'__20
d_'42''45'pres'45''8739'_74 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'42''45'pres'45''8739'_74 v4 v5
du_'42''45'pres'45''8739'_74 ::
  T__'8739'__20 -> T__'8739'__20 -> T__'8739'__20
du_'42''45'pres'45''8739'_74 v0 v1
  = case coe v0 of
      C_divides_34 v2
        -> case coe v1 of
             C_divides_34 v4 -> coe C_divides_34 (mulInt (coe v2) (coe v4))
             _               -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
