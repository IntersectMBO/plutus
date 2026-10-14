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

module MAlonzo.Code.Builtin.ByteString.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Builtin.ByteString.Byte
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Vec.Base

import FFI.ByteString
-- Builtin.ByteString.Base.ByteString
d_ByteString_6 = ()
type T_ByteString_6 = ByteString
pattern C_'91''93'_8 = BSNil
pattern C__'8759'__10 a0 a1 = BSCons a0 a1
check_'91''93'_8 :: T_ByteString_6
check_'91''93'_8 = BSNil
check__'8759'__10 ::
  MAlonzo.Code.Builtin.ByteString.Byte.T_Byte_6 ->
  T_ByteString_6 -> T_ByteString_6
check__'8759'__10 = BSCons
cover_ByteString_6 :: ByteString -> ()
cover_ByteString_6 x
  = case x of
      BSNil -> ()
      BSCons _ _ -> ()
-- Builtin.ByteString.Base.eqByteString
d_eqByteString_12 :: T_ByteString_6 -> T_ByteString_6 -> Bool
d_eqByteString_12 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_'91''93'_8
           -> case coe v1 of
                C_'91''93'_8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C__'8759'__10 v3 v4
           -> case coe v1 of
                C__'8759'__10 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe
                          MAlonzo.Code.Builtin.ByteString.Byte.d_eqByte_70 (coe v3) (coe v5))
                       (coe d_eqByteString_12 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Builtin.ByteString.Base.fromHex
d_fromHex_22 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe T_ByteString_6
d_fromHex_22 v0
  = coe
      du_go_42
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Builtin.ByteString.Base._.hexDigit
d_hexDigit_30 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe Integer
d_hexDigit_30 ~v0 v1 = du_hexDigit_30 v1
du_hexDigit_30 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe Integer
du_hexDigit_30 v0
  = let v1
          = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0 in
    coe
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
               (coe (48 :: Integer)) (coe v1))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v1)
               (coe (57 :: Integer))))
         (coe
            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
            (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 (48 :: Integer)))
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe
               MAlonzo.Code.Data.Bool.Base.d__'8743'__24
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                  (coe (65 :: Integer)) (coe v1))
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v1)
                  (coe (70 :: Integer))))
            (coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 (55 :: Integer)))
            (coe
               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
               (coe
                  MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                     (coe (97 :: Integer)) (coe v1))
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v1)
                     (coe (102 :: Integer))))
               (coe
                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                  (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 (87 :: Integer)))
               (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))
-- Builtin.ByteString.Base._.go
d_go_42 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Maybe T_ByteString_6
d_go_42 ~v0 v1 = du_go_42 v1
du_go_42 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Maybe T_ByteString_6
du_go_42 v0
  = case coe v0 of
      []
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_'91''93'_8)
      (:) v1 v2
        -> case coe v2 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_hexDigit_30 (coe v1))
                    (coe
                       (\ v5 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_hexDigit_30 (coe v3))
                            (coe
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                                    (coe du_go_42 (coe v4))
                                    (coe
                                       (\ v7 ->
                                          coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               C__'8759'__10
                                               (coe
                                                  MAlonzo.Code.Builtin.ByteString.Byte.d_ℕToByte_190
                                                  (coe
                                                     addInt
                                                     (coe mulInt (coe (16 :: Integer)) (coe v5))
                                                     (coe v6)))
                                               (coe v7))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.mkByteString
d_mkByteString_56 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_ByteString_6
d_mkByteString_56 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe_32 (coe (\ v1 -> v1))
      (coe C_'91''93'_8) (coe d_fromHex_22 (coe v0))
-- Builtin.ByteString.Base.lengthℕ
d_lengthℕ_62 :: T_ByteString_6 -> Integer
d_lengthℕ_62 v0
  = case coe v0 of
      C_'91''93'_8 -> coe (0 :: Integer)
      C__'8759'__10 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe d_lengthℕ_62 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.take
d_take_66 :: Integer -> T_ByteString_6 -> T_ByteString_6
d_take_66 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110 (coe v0)
         (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
      (coe C_'91''93'_8)
      (coe du_'46'extendedlambda0_72 (coe v0) (coe v1))
-- Builtin.ByteString.Base..extendedlambda0
d_'46'extendedlambda0_72 ::
  Integer -> T_ByteString_6 -> T_ByteString_6 -> T_ByteString_6
d_'46'extendedlambda0_72 v0 ~v1 v2
  = du_'46'extendedlambda0_72 v0 v2
du_'46'extendedlambda0_72 ::
  Integer -> T_ByteString_6 -> T_ByteString_6
du_'46'extendedlambda0_72 v0 v1
  = case coe v1 of
      C_'91''93'_8 -> coe v1
      C__'8759'__10 v2 v3
        -> coe
             C__'8759'__10 (coe v2)
             (coe
                d_take_66
                (coe
                   MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0)
                   (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.dropB
d_dropB_78 :: Integer -> T_ByteString_6 -> T_ByteString_6
d_dropB_78 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110 (coe v0)
         (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
      (coe v1) (coe du_'46'extendedlambda1_84 (coe v0) (coe v1))
-- Builtin.ByteString.Base..extendedlambda1
d_'46'extendedlambda1_84 ::
  Integer -> T_ByteString_6 -> T_ByteString_6 -> T_ByteString_6
d_'46'extendedlambda1_84 v0 ~v1 v2
  = du_'46'extendedlambda1_84 v0 v2
du_'46'extendedlambda1_84 ::
  Integer -> T_ByteString_6 -> T_ByteString_6
du_'46'extendedlambda1_84 v0 v1
  = case coe v1 of
      C_'91''93'_8 -> coe v1
      C__'8759'__10 v2 v3
        -> coe
             d_dropB_78
             (coe
                MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0)
                (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.replicateBS
d_replicateBS_88 ::
  Integer ->
  MAlonzo.Code.Builtin.ByteString.Byte.T_Byte_6 -> T_ByteString_6
d_replicateBS_88 v0 v1
  = case coe v0 of
      0 -> coe C_'91''93'_8
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                C__'8759'__10 (coe v1) (coe d_replicateBS_88 (coe v2) (coe v1)))
-- Builtin.ByteString.Base._++ᵇ_
d__'43''43''7495'__94 ::
  T_ByteString_6 -> T_ByteString_6 -> T_ByteString_6
d__'43''43''7495'__94 v0 v1
  = case coe v0 of
      C_'91''93'_8 -> coe v1
      C__'8759'__10 v2 v3
        -> coe
             C__'8759'__10 (coe v2)
             (coe d__'43''43''7495'__94 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.reverseAcc
d_reverseAcc_104 ::
  T_ByteString_6 -> T_ByteString_6 -> T_ByteString_6
d_reverseAcc_104 v0 v1
  = case coe v1 of
      C_'91''93'_8 -> coe v0
      C__'8759'__10 v2 v3
        -> coe
             d_reverseAcc_104 (coe C__'8759'__10 (coe v2) (coe v0)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.reverseBS
d_reverseBS_114 :: T_ByteString_6 -> T_ByteString_6
d_reverseBS_114 = coe d_reverseAcc_104 (coe C_'91''93'_8)
-- Builtin.ByteString.Base.mapBS
d_mapBS_116 ::
  (MAlonzo.Code.Builtin.ByteString.Byte.T_Byte_6 ->
   MAlonzo.Code.Builtin.ByteString.Byte.T_Byte_6) ->
  T_ByteString_6 -> T_ByteString_6
d_mapBS_116 v0 v1
  = case coe v1 of
      C_'91''93'_8 -> coe v1
      C__'8759'__10 v2 v3
        -> coe
             C__'8759'__10 (coe v0 v2) (coe d_mapBS_116 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.zipWithBS
d_zipWithBS_130 ::
  (MAlonzo.Code.Builtin.ByteString.Byte.T_Byte_6 ->
   MAlonzo.Code.Builtin.ByteString.Byte.T_Byte_6 ->
   MAlonzo.Code.Builtin.ByteString.Byte.T_Byte_6) ->
  Bool ->
  MAlonzo.Code.Builtin.ByteString.Byte.T_Byte_6 ->
  T_ByteString_6 -> T_ByteString_6 -> T_ByteString_6
d_zipWithBS_130 v0 v1 v2 v3 v4
  = case coe v3 of
      C_'91''93'_8
        -> case coe v4 of
             C_'91''93'_8 -> coe v4
             C__'8759'__10 v5 v6
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v1)
                    (coe
                       C__'8759'__10 (coe v0 v2 v5)
                       (coe d_zipWithBS_130 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8759'__10 v5 v6
        -> case coe v4 of
             C_'91''93'_8
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v1)
                    (coe
                       C__'8759'__10 (coe v0 v5 v2)
                       (coe d_zipWithBS_130 (coe v0) (coe v1) (coe v2) (coe v6) (coe v4)))
                    (coe v4)
             C__'8759'__10 v7 v8
               -> coe
                    C__'8759'__10 (coe v0 v5 v7)
                    (coe d_zipWithBS_130 (coe v0) (coe v1) (coe v2) (coe v6) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.Bits*
d_Bits'42'_172 :: ()
d_Bits'42'_172 = erased
-- Builtin.ByteString.Base.toBitsAcc
d_toBitsAcc_174 :: [Bool] -> T_ByteString_6 -> [Bool]
d_toBitsAcc_174 v0 v1
  = case coe v1 of
      C_'91''93'_8 -> coe v0
      C__'8759'__10 v2 v3
        -> coe
             d_toBitsAcc_174
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Data.Vec.Base.du_toList_592
                   (coe
                      MAlonzo.Code.Builtin.ByteString.Byte.d_byteToBits_112 (coe v2)))
                (coe v0))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.toBits
d_toBits_184 :: T_ByteString_6 -> [Bool]
d_toBits_184
  = coe
      d_toBitsAcc_174 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Builtin.ByteString.Base.fromBitsAcc
d_fromBitsAcc_186 :: T_ByteString_6 -> [Bool] -> T_ByteString_6
d_fromBitsAcc_186 v0 v1
  = case coe v1 of
      (:) v2 v3
        -> case coe v3 of
             (:) v4 v5
               -> case coe v5 of
                    (:) v6 v7
                      -> case coe v7 of
                           (:) v8 v9
                             -> case coe v9 of
                                  (:) v10 v11
                                    -> case coe v11 of
                                         (:) v12 v13
                                           -> case coe v13 of
                                                (:) v14 v15
                                                  -> case coe v15 of
                                                       (:) v16 v17
                                                         -> coe
                                                              d_fromBitsAcc_186
                                                              (coe
                                                                 C__'8759'__10
                                                                 (coe
                                                                    MAlonzo.Code.Builtin.ByteString.Byte.d_bitsToByte_130
                                                                    (coe
                                                                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                                       v2
                                                                       (coe
                                                                          MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                                          v4
                                                                          (coe
                                                                             MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                                             v6
                                                                             (coe
                                                                                MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                                                v8
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                                                   v10
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                                                      v12
                                                                                      (coe
                                                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                                                         v14
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                                                            v16
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))))))))))
                                                                 (coe v0))
                                                              (coe v17)
                                                       _ -> coe v0
                                                _ -> coe v0
                                         _ -> coe v0
                                  _ -> coe v0
                           _ -> coe v0
                    _ -> coe v0
             _ -> coe v0
      _ -> coe v0
-- Builtin.ByteString.Base.fromBits
d_fromBits_210 :: [Bool] -> T_ByteString_6
d_fromBits_210 = coe d_fromBitsAcc_186 (coe C_'91''93'_8)
-- Builtin.ByteString.Base.lookupBit
d_lookupBit_212 :: [Bool] -> Integer -> Maybe Bool
d_lookupBit_212 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_lookupBit_212 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.setBit
d_setBit_224 :: Integer -> Bool -> [Bool] -> [Bool]
d_setBit_224 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v0 of
             0 -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v4)
             _ -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
                  coe
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                       (coe d_setBit_224 (coe v5) (coe v1) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.firstSetBitFrom
d_firstSetBitFrom_240 :: Integer -> [Bool] -> Integer
d_firstSetBitFrom_240 v0 v1
  = case coe v1 of
      [] -> coe (-1 :: Integer)
      (:) v2 v3
        -> if coe v2
             then coe v0
             else coe
                    d_firstSetBitFrom_240 (coe addInt (coe (1 :: Integer)) (coe v0))
                    (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.firstSetBit
d_firstSetBit_250 :: [Bool] -> Integer
d_firstSetBit_250 = coe d_firstSetBitFrom_240 (coe (0 :: Integer))
-- Builtin.ByteString.Base.shiftBits
d_shiftBits_252 :: Integer -> [Bool] -> [Bool]
d_shiftBits_252 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
         (coe du_n_262 (coe v1))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Base.du_replicate_278
         (coe du_n_262 (coe v1))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe du_shifted_264 (coe v1) (coe v0))
-- Builtin.ByteString.Base._.n
d_n_262 :: Integer -> [Bool] -> Integer
d_n_262 ~v0 v1 = du_n_262 v1
du_n_262 :: [Bool] -> Integer
du_n_262 v0 = coe MAlonzo.Code.Data.List.Base.du_length_268 v0
-- Builtin.ByteString.Base._.shifted
d_shifted_264 :: Integer -> [Bool] -> Integer -> [Bool]
d_shifted_264 ~v0 v1 v2 = du_shifted_264 v1 v2
du_shifted_264 :: [Bool] -> Integer -> [Bool]
du_shifted_264 v0 v1
  = case coe v1 of
      _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Data.List.Base.du_replicate_278 (coe v1)
               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
            (coe
               MAlonzo.Code.Data.List.Base.du_take_530
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (coe du_n_262 (coe v0))
                  v1)
               (coe v0))
      _ -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Data.List.Base.du_drop_542
                (coe subInt (coe (0 :: Integer)) (coe v1)) (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du_replicate_278
                (coe subInt (coe (0 :: Integer)) (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
-- Builtin.ByteString.Base.rotateBits
d_rotateBits_270 :: Integer -> [Bool] -> [Bool]
d_rotateBits_270 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Data.List.Base.du_drop_542
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                   (coe du_n_282 (coe v2) (coe v3))
                   (d_r_284 (coe v0) (coe v2) (coe v3)))
                (coe v1))
             (coe
                MAlonzo.Code.Data.List.Base.du_take_530
                (coe
                   MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                   (coe du_n_282 (coe v2) (coe v3))
                   (d_r_284 (coe v0) (coe v2) (coe v3)))
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base._.n
d_n_282 :: Integer -> Bool -> [Bool] -> Integer
d_n_282 ~v0 v1 v2 = du_n_282 v1 v2
du_n_282 :: Bool -> [Bool] -> Integer
du_n_282 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))
-- Builtin.ByteString.Base._.r
d_r_284 :: Integer -> Bool -> [Bool] -> Integer
d_r_284 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.du__'37'ℕ__414 (coe v0)
      (coe du_n_282 (coe v1) (coe v2))
-- Builtin.ByteString.Base.byteStringToℕAcc
d_byteStringToℕAcc_286 :: Integer -> T_ByteString_6 -> Integer
d_byteStringToℕAcc_286 v0 v1
  = case coe v1 of
      C_'91''93'_8 -> coe v0
      C__'8759'__10 v2 v3
        -> coe
             d_byteStringToℕAcc_286
             (coe
                addInt
                (coe MAlonzo.Code.Builtin.ByteString.Byte.d_byteToℕ_194 (coe v2))
                (coe mulInt (coe v0) (coe (256 :: Integer))))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Base.byteStringToℕ
d_byteStringToℕ_296 :: T_ByteString_6 -> Integer
d_byteStringToℕ_296
  = coe d_byteStringToℕAcc_286 (coe (0 :: Integer))
-- Builtin.ByteString.Base.digits256
d_digits256_298 :: Integer -> Integer -> Maybe T_ByteString_6
d_digits256_298 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_'91''93'_8)
      _ -> case coe v0 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
                  coe
                    (coe
                       MAlonzo.Code.Data.Maybe.Base.du_map_64
                       (coe
                          C__'8759'__10
                          (coe
                             MAlonzo.Code.Builtin.ByteString.Byte.d_ℕToByte_190
                             (coe
                                MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v1)
                                (coe (256 :: Integer)))))
                       (d_digits256_298
                          (coe v2)
                          (coe
                             MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1)
                             (coe (256 :: Integer)))))
-- Builtin.ByteString.Base.ℕToByteString
d_ℕToByteString_310 ::
  Bool -> Integer -> Integer -> Maybe T_ByteString_6
d_ℕToByteString_310 v0 v1 v2
  = case coe v2 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                d_replicateBS_88 (coe v1)
                (coe
                   MAlonzo.Code.Builtin.ByteString.Byte.C_byte_24
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (let v4
                    = coe
                        MAlonzo.Code.Data.Maybe.Base.du_maybe_32
                        (coe
                           (\ v4 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                (coe
                                   C__'8759'__10
                                   (coe
                                      MAlonzo.Code.Builtin.ByteString.Byte.d_ℕToByte_190
                                      (coe
                                         MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v2)
                                         (coe (256 :: Integer))))
                                   (coe v4))))
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                        (coe
                           d_digits256_298 (coe (8191 :: Integer))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60 (0 :: Integer)
                              (255 :: Integer) v3 (254 :: Integer))) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                             (coe eqInt (coe v1) (coe (0 :: Integer)))
                             (coe
                                MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                (coe d_lengthℕ_62 (coe v5)) (coe v1)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0)
                                (coe
                                   d__'43''43''7495'__94
                                   (coe
                                      d_replicateBS_88
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
                                         (d_lengthℕ_62 (coe v5)))
                                      (coe
                                         MAlonzo.Code.Builtin.ByteString.Byte.C_byte_24
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))
                                   (coe d_reverseBS_114 v5))
                                (coe
                                   d__'43''43''7495'__94 (coe v5)
                                   (coe
                                      d_replicateBS_88
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
                                         (d_lengthℕ_62 (coe v5)))
                                      (coe
                                         MAlonzo.Code.Builtin.ByteString.Byte.C_byte_24
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))))))
                          (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                   _ -> MAlonzo.RTE.mazUnreachableError))
