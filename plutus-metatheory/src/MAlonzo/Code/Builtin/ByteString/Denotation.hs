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

module MAlonzo.Code.Builtin.ByteString.Denotation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Builtin.ByteString.Base
import qualified MAlonzo.Code.Builtin.ByteString.Byte
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.ListAction
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Builtin.ByteString.Denotation.lengthBS
d_lengthBS_6 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 -> Integer
d_lengthBS_6 v0
  = case coe v0 of
      MAlonzo.Code.Builtin.ByteString.Base.C_'91''93'_8
        -> coe (0 :: Integer)
      MAlonzo.Code.Builtin.ByteString.Base.C__'8759'__10 v1 v2
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe (1 :: Integer))
             (coe d_lengthBS_6 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Denotation.concat
d_concat_10 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_concat_10 v0 v1
  = case coe v0 of
      MAlonzo.Code.Builtin.ByteString.Base.C_'91''93'_8 -> coe v1
      MAlonzo.Code.Builtin.ByteString.Base.C__'8759'__10 v2 v3
        -> coe
             MAlonzo.Code.Builtin.ByteString.Base.C__'8759'__10 (coe v2)
             (coe d_concat_10 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Denotation.equals
d_equals_20 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 -> Bool
d_equals_20
  = coe MAlonzo.Code.Builtin.ByteString.Base.d_eqByteString_12
-- Builtin.ByteString.Denotation.B<=
d_B'60''61'_22 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 -> Bool
d_B'60''61'_22 v0 v1
  = case coe v0 of
      MAlonzo.Code.Builtin.ByteString.Base.C_'91''93'_8
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Builtin.ByteString.Base.C__'8759'__10 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Builtin.ByteString.Base.C_'91''93'_8
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Builtin.ByteString.Base.C__'8759'__10 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       ltInt
                       (coe MAlonzo.Code.Builtin.ByteString.Byte.d_byteToℕ_198 (coe v2))
                       (coe MAlonzo.Code.Builtin.ByteString.Byte.d_byteToℕ_198 (coe v4)))
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          eqInt
                          (coe MAlonzo.Code.Builtin.ByteString.Byte.d_byteToℕ_198 (coe v2))
                          (coe MAlonzo.Code.Builtin.ByteString.Byte.d_byteToℕ_198 (coe v4)))
                       (coe d_B'60''61'_22 (coe v3) (coe v5))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Denotation.B<
d_B'60'_32 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 -> Bool
d_B'60'_32 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe d_B'60''61'_22 (coe v0) (coe v1))
      (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe d_equals_20 v0 v1))
-- Builtin.ByteString.Denotation.cons
d_cons_38 ::
  Integer ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  Maybe MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_cons_38 v0 v1
  = let v2
          = MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880
              (coe (0 :: Integer)) (coe v0) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110 (coe v0)
                             (coe (255 :: Integer)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.Builtin.ByteString.Base.C__'8759'__10
                                (coe MAlonzo.Code.Builtin.ByteString.Byte.du_ℤToByte_206 (coe v0))
                                (coe v1)))
                          (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Builtin.ByteString.Denotation.slice
d_slice_64 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_slice_64 v0 v1 v2
  = coe
      MAlonzo.Code.Builtin.ByteString.Base.d_take_66 (coe v1)
      (coe
         MAlonzo.Code.Builtin.ByteString.Base.d_dropB_78 (coe v0) (coe v2))
-- Builtin.ByteString.Denotation.index
d_index_72 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  Integer -> Maybe Integer
d_index_72 v0 v1
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_map_64
      MAlonzo.Code.Builtin.ByteString.Byte.d_byteToℤ_210
      (coe
         du_go_82 (coe v1) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12)
         (coe v0))
-- Builtin.ByteString.Denotation._.go
d_go_82 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  Maybe MAlonzo.Code.Builtin.ByteString.Byte.T_Byte_6
d_go_82 ~v0 v1 v2 v3 = du_go_82 v1 v2 v3
du_go_82 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  Maybe MAlonzo.Code.Builtin.ByteString.Byte.T_Byte_6
du_go_82 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Builtin.ByteString.Base.C_'91''93'_8
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Builtin.ByteString.Base.C__'8759'__10 v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe
                   MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800 (coe v1)
                   (coe v0)))
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3))
             (coe
                du_go_82 (coe v0)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1)
                   (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Denotation.bitLength
d_bitLength_90 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 -> Integer
d_bitLength_90 v0
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__316
      (coe d_lengthBS_6 (coe v0)) (coe (8 :: Integer))
-- Builtin.ByteString.Denotation.validBitIndex
d_validBitIndex_94 :: Integer -> Integer -> Bool
d_validBitIndex_94 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
         (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v1))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
         (coe
            MAlonzo.Code.Data.Integer.Properties.d__'60''63'__3190 (coe v1)
            (coe v0)))
-- Builtin.ByteString.Denotation.fitsInt
d_fitsInt_100 :: Integer -> Bool
d_fitsInt_100 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
         (coe (-9223372036854775808 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110 (coe v0)
         (coe (9223372036854775807 :: Integer)))
-- Builtin.ByteString.Denotation.BStoI
d_BStoI_104 ::
  Bool ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 -> Integer
d_BStoI_104 v0 v1
  = if coe v0
      then coe
             MAlonzo.Code.Builtin.ByteString.Base.d_byteStringToℕ_302 v1
      else coe
             MAlonzo.Code.Builtin.ByteString.Base.d_byteStringToℕ_302
             (coe MAlonzo.Code.Builtin.ByteString.Base.d_reverseBS_104 v1)
-- Builtin.ByteString.Denotation.ItoBS
d_ItoBS_110 ::
  Bool ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_ItoBS_110 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
            (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v1))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110 (coe v1)
               (coe (8192 :: Integer)))
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
               (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v2))))
      (coe
         MAlonzo.Code.Builtin.ByteString.Base.d_ℕToByteString_330 (coe v0)
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Builtin.ByteString.Denotation.andBYTESTRING
d_andBYTESTRING_118 ::
  Bool ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_andBYTESTRING_118 v0
  = coe
      MAlonzo.Code.Builtin.ByteString.Base.d_zipWithBS_134
      (coe MAlonzo.Code.Builtin.ByteString.Byte.d_andByte_218) (coe v0)
      (coe
         MAlonzo.Code.Builtin.ByteString.Byte.C_byte_24
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
-- Builtin.ByteString.Denotation.orBYTESTRING
d_orBYTESTRING_122 ::
  Bool ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_orBYTESTRING_122 v0
  = coe
      MAlonzo.Code.Builtin.ByteString.Base.d_zipWithBS_134
      (coe MAlonzo.Code.Builtin.ByteString.Byte.d_orByte_224) (coe v0)
      (coe
         MAlonzo.Code.Builtin.ByteString.Byte.C_byte_24
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
-- Builtin.ByteString.Denotation.xorBYTESTRING
d_xorBYTESTRING_126 ::
  Bool ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_xorBYTESTRING_126 v0
  = coe
      MAlonzo.Code.Builtin.ByteString.Base.d_zipWithBS_134
      (coe MAlonzo.Code.Builtin.ByteString.Byte.d_xorByte_230) (coe v0)
      (coe
         MAlonzo.Code.Builtin.ByteString.Byte.C_byte_24
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
-- Builtin.ByteString.Denotation.complementBYTESTRING
d_complementBYTESTRING_130 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_complementBYTESTRING_130
  = coe
      MAlonzo.Code.Builtin.ByteString.Base.d_mapBS_120
      (coe MAlonzo.Code.Builtin.ByteString.Byte.d_notByte_236)
-- Builtin.ByteString.Denotation.readBIT
d_readBIT_132 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  Integer -> Maybe Bool
d_readBIT_132 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_validBitIndex_94 (coe d_bitLength_90 (coe v0)) (coe v1))
      (coe
         MAlonzo.Code.Builtin.ByteString.Base.d_lookupBit_224
         (coe MAlonzo.Code.Builtin.ByteString.Base.d_toBits_178 v0)
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Builtin.ByteString.Denotation.writeBITS
d_writeBITS_138 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  [Integer] ->
  Bool -> Maybe MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_writeBITS_138 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.Bool.ListAction.du_all_18
         (coe d_validBitIndex_94 (coe d_bitLength_90 (coe v0))) (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
         (coe
            MAlonzo.Code.Builtin.ByteString.Base.d_fromBits_194
            (coe
               MAlonzo.Code.Data.List.Base.du_foldr_216
               (coe
                  (\ v3 ->
                     MAlonzo.Code.Builtin.ByteString.Base.d_setBit_236
                       (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v3))
                       (coe v2)))
               (coe MAlonzo.Code.Builtin.ByteString.Base.d_toBits_178 v0)
               (coe v1))))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Builtin.ByteString.Denotation.replicateBYTE
d_replicateBYTE_148 ::
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_replicateBYTE_148 v0 v1
  = let v2
          = MAlonzo.Code.Builtin.ByteString.Byte.d_toByte_214 (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                   (coe
                      MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
                      (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v0))
                   (coe
                      MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110 (coe v0)
                      (coe (8192 :: Integer))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe
                      MAlonzo.Code.Builtin.ByteString.Base.d_replicateBS_88
                      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                      (coe v3)))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Builtin.ByteString.Denotation.shiftBYTESTRING
d_shiftBYTESTRING_168 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  Integer ->
  Maybe MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_shiftBYTESTRING_168 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_fitsInt_100 (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
         (coe
            MAlonzo.Code.Builtin.ByteString.Base.d_fromBits_194
            (MAlonzo.Code.Builtin.ByteString.Base.d_shiftBits_268
               (coe v1)
               (coe MAlonzo.Code.Builtin.ByteString.Base.d_toBits_178 v0))))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Builtin.ByteString.Denotation.rotateBYTESTRING
d_rotateBYTESTRING_174 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 ->
  Integer ->
  Maybe MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6
d_rotateBYTESTRING_174 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_fitsInt_100 (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
         (coe
            MAlonzo.Code.Builtin.ByteString.Base.d_fromBits_194
            (MAlonzo.Code.Builtin.ByteString.Base.d_rotateBits_286
               (coe v1)
               (coe MAlonzo.Code.Builtin.ByteString.Base.d_toBits_178 v0))))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Builtin.ByteString.Denotation.countSetBITS
d_countSetBITS_180 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 -> Integer
d_countSetBITS_180 v0
  = case coe v0 of
      MAlonzo.Code.Builtin.ByteString.Base.C_'91''93'_8
        -> coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
      MAlonzo.Code.Builtin.ByteString.Base.C__'8759'__10 v1 v2
        -> coe
             MAlonzo.Code.Data.Integer.Base.d__'43'__284
             (coe MAlonzo.Code.Builtin.ByteString.Byte.d_popCount_240 (coe v1))
             (coe d_countSetBITS_180 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.ByteString.Denotation.findFirstSetBIT
d_findFirstSetBIT_186 ::
  MAlonzo.Code.Builtin.ByteString.Base.T_ByteString_6 -> Integer
d_findFirstSetBIT_186 v0
  = coe
      MAlonzo.Code.Builtin.ByteString.Base.d_firstSetBit_252
      (coe MAlonzo.Code.Builtin.ByteString.Base.d_toBits_178 v0)
