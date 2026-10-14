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

module MAlonzo.Code.Builtin.ByteString.Byte where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.Properties
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Parity.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

import FFI.ByteString
-- Builtin.ByteString.Byte.Byte
d_Byte_6 = ()
type T_Byte_6 = Byte
pattern C_byte_24 a0 a1 a2 a3 a4 a5 a6 a7 = Byte a0 a1 a2 a3 a4 a5 a6 a7
check_byte_24 ::
  Bool ->
  Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> T_Byte_6
check_byte_24 = Byte
cover_Byte_6 :: Byte -> ()
cover_Byte_6 x
  = case x of
      Byte _ _ _ _ _ _ _ _ -> ()
-- Builtin.ByteString.Byte.ᵇproj₁
d_'7495'proj'8321'_26 :: T_Byte_6 -> Bool
d_'7495'proj'8321'_26 v0
  = case coe v0 of
      C_byte_24 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.ᵇproj₂
d_'7495'proj'8322'_28 :: T_Byte_6 -> Bool
d_'7495'proj'8322'_28 v0
  = case coe v0 of
      C_byte_24 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.ᵇproj₃
d_'7495'proj'8323'_30 :: T_Byte_6 -> Bool
d_'7495'proj'8323'_30 v0
  = case coe v0 of
      C_byte_24 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.ᵇproj₄
d_'7495'proj'8324'_32 :: T_Byte_6 -> Bool
d_'7495'proj'8324'_32 v0
  = case coe v0 of
      C_byte_24 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.ᵇproj₅
d_'7495'proj'8325'_34 :: T_Byte_6 -> Bool
d_'7495'proj'8325'_34 v0
  = case coe v0 of
      C_byte_24 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.ᵇproj₆
d_'7495'proj'8326'_36 :: T_Byte_6 -> Bool
d_'7495'proj'8326'_36 v0
  = case coe v0 of
      C_byte_24 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.ᵇproj₇
d_'7495'proj'8327'_38 :: T_Byte_6 -> Bool
d_'7495'proj'8327'_38 v0
  = case coe v0 of
      C_byte_24 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.ᵇproj₈
d_'7495'proj'8328'_40 :: T_Byte_6 -> Bool
d_'7495'proj'8328'_40 v0
  = case coe v0 of
      C_byte_24 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.eqByte
d_eqByte_70 :: T_Byte_6 -> T_Byte_6 -> Bool
d_eqByte_70 v0 v1
  = case coe v0 of
      C_byte_24 v2 v3 v4 v5 v6 v7 v8 v9
        -> case coe v1 of
             C_byte_24 v10 v11 v12 v13 v14 v15 v16 v17
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe
                          MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v2)
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                          (coe
                             MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v3)
                             (coe v11)))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                             (coe
                                MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v4)
                                (coe v12)))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                             (coe
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                (coe
                                   MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v5)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                (coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                   (coe
                                      MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v6)
                                      (coe v14)))
                                (coe
                                   MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                      (coe
                                         MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v7)
                                         (coe v15)))
                                   (coe
                                      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                         (coe
                                            MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196
                                            (coe v8) (coe v16)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                         (coe
                                            MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196
                                            (coe v9) (coe v17)))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.Bits
d_Bits_108 :: Integer -> ()
d_Bits_108 = erased
-- Builtin.ByteString.Byte.byteToBits
d_byteToBits_112 :: T_Byte_6 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_byteToBits_112 v0
  = case coe v0 of
      C_byte_24 v1 v2 v3 v4 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v8
             (coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7
                (coe
                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                   (coe
                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v5
                      (coe
                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4
                         (coe
                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3
                            (coe
                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2
                               (coe
                                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v1
                                  (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.bitsToByte
d_bitsToByte_130 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> T_Byte_6
d_bitsToByte_130 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v8 v9
                      -> case coe v9 of
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v14 v15
                                    -> case coe v15 of
                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v17 v18
                                           -> case coe v18 of
                                                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v20 v21
                                                  -> case coe v21 of
                                                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v23 v24
                                                         -> coe
                                                              seq (coe v24)
                                                              (coe
                                                                 C_byte_24 (coe v23) (coe v20)
                                                                 (coe v17) (coe v14) (coe v11)
                                                                 (coe v8) (coe v5) (coe v2))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.addBits
d_addBits_150 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_addBits_150 ~v0 v1 v2 v3 = du_addBits_150 v1 v2 v3
du_addBits_150 ::
  Bool ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_addBits_150 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe seq (coe v2) (coe v1)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
               -> coe
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                    (MAlonzo.Code.Data.Bool.Base.d__xor__36
                       (coe v0)
                       (coe MAlonzo.Code.Data.Bool.Base.d__xor__36 (coe v4) (coe v7)))
                    (coe
                       du_addBits_150
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                          (coe MAlonzo.Code.Data.Bool.Base.d__'8743'__24 (coe v4) (coe v7))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24 (coe v0)
                             (coe MAlonzo.Code.Data.Bool.Base.d__xor__36 (coe v4) (coe v7))))
                       (coe v5) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.plusByte
d_plusByte_164 :: T_Byte_6 -> T_Byte_6 -> T_Byte_6
d_plusByte_164 v0 v1
  = coe
      d_bitsToByte_130
      (coe
         du_addBits_150 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe d_byteToBits_112 (coe v0)) (coe d_byteToBits_112 (coe v1)))
-- Builtin.ByteString.Byte.ℕToBits
d_ℕToBits_172 ::
  Integer -> Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_ℕToBits_172 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                (coe
                   du_lsb_182 (coe MAlonzo.Code.Data.Nat.Base.d_parity_264 (coe v1)))
                (d_ℕToBits_172
                   (coe v2)
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d_'8970'_'47'2'8971'_268 (coe v1))))
-- Builtin.ByteString.Byte._.lsb
d_lsb_182 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Parity.Base.T_Parity_6 -> Bool
d_lsb_182 ~v0 ~v1 v2 = du_lsb_182 v2
du_lsb_182 :: MAlonzo.Code.Data.Parity.Base.T_Parity_6 -> Bool
du_lsb_182 v0
  = case coe v0 of
      MAlonzo.Code.Data.Parity.Base.C_0ℙ_8
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Data.Parity.Base.C_1ℙ_10
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Byte.bitsToℕ
d_bitsToℕ_186 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_bitsToℕ_186 v0 v1
  = case coe v0 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
                  -> coe
                       addInt
                       (coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v4)
                          (coe (1 :: Integer)) (coe (0 :: Integer)))
                       (coe
                          mulInt (coe (2 :: Integer)) (coe d_bitsToℕ_186 (coe v2) (coe v5)))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Builtin.ByteString.Byte.ℕToByte
d_ℕToByte_194 :: Integer -> T_Byte_6
d_ℕToByte_194 v0
  = coe
      d_bitsToByte_130 (coe d_ℕToBits_172 (coe (8 :: Integer)) (coe v0))
-- Builtin.ByteString.Byte.byteToℕ
d_byteToℕ_198 :: T_Byte_6 -> Integer
d_byteToℕ_198 v0
  = coe
      d_bitsToℕ_186 (coe (8 :: Integer)) (coe d_byteToBits_112 (coe v0))
-- Builtin.ByteString.Byte.ℤToByte
d_ℤToByte_206 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 -> T_Byte_6
d_ℤToByte_206 v0 ~v1 = du_ℤToByte_206 v0
du_ℤToByte_206 :: Integer -> T_Byte_6
du_ℤToByte_206 v0 = coe d_ℕToByte_194 (coe v0)
-- Builtin.ByteString.Byte.byteToℤ
d_byteToℤ_210 :: T_Byte_6 -> Integer
d_byteToℤ_210 v0 = coe d_byteToℕ_198 (coe v0)
-- Builtin.ByteString.Byte.toByte
d_toByte_214 :: Integer -> Maybe T_Byte_6
d_toByte_214 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0)
               (coe (255 :: Integer)))
            (coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe d_ℕToByte_194 (coe v0)))
            (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Builtin.ByteString.Byte.andByte
d_andByte_218 :: T_Byte_6 -> T_Byte_6 -> T_Byte_6
d_andByte_218 v0 v1
  = coe
      d_bitsToByte_130
      (coe
         MAlonzo.Code.Data.Vec.Base.du_zipWith_242
         (coe MAlonzo.Code.Data.Bool.Base.d__'8743'__24)
         (coe d_byteToBits_112 (coe v0)) (coe d_byteToBits_112 (coe v1)))
-- Builtin.ByteString.Byte.orByte
d_orByte_224 :: T_Byte_6 -> T_Byte_6 -> T_Byte_6
d_orByte_224 v0 v1
  = coe
      d_bitsToByte_130
      (coe
         MAlonzo.Code.Data.Vec.Base.du_zipWith_242
         (coe MAlonzo.Code.Data.Bool.Base.d__'8744'__30)
         (coe d_byteToBits_112 (coe v0)) (coe d_byteToBits_112 (coe v1)))
-- Builtin.ByteString.Byte.xorByte
d_xorByte_230 :: T_Byte_6 -> T_Byte_6 -> T_Byte_6
d_xorByte_230 v0 v1
  = coe
      d_bitsToByte_130
      (coe
         MAlonzo.Code.Data.Vec.Base.du_zipWith_242
         (coe MAlonzo.Code.Data.Bool.Base.d__xor__36)
         (coe d_byteToBits_112 (coe v0)) (coe d_byteToBits_112 (coe v1)))
-- Builtin.ByteString.Byte.notByte
d_notByte_236 :: T_Byte_6 -> T_Byte_6
d_notByte_236 v0
  = coe
      d_bitsToByte_130
      (coe
         MAlonzo.Code.Data.Vec.Base.du_map_178
         (coe MAlonzo.Code.Data.Bool.Base.d_not_22)
         (coe d_byteToBits_112 (coe v0)))
-- Builtin.ByteString.Byte.popCount
d_popCount_240 :: T_Byte_6 -> Integer
d_popCount_240 v0
  = coe du_count_250 (coe d_byteToBits_112 (coe v0))
-- Builtin.ByteString.Byte._.count
d_count_250 ::
  T_Byte_6 ->
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_count_250 ~v0 ~v1 v2 = du_count_250 v2
du_count_250 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
du_count_250 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe (0 :: Integer)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2 v3
        -> coe
             addInt (coe du_count_250 (coe v3))
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v2)
                (coe (1 :: Integer)) (coe (0 :: Integer)))
      _ -> MAlonzo.RTE.mazUnreachableError
