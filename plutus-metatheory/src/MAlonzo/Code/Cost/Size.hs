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

module MAlonzo.Code.Cost.Size where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Int
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Cost.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Utils

import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Evaluation.Machine.CostStream
import Data.SatInt
size = fromSatInt . sumCostStream . flattenCostRose . memoryUsage
-- Cost.Size.integerSize
d_integerSize_4 :: Integer -> Integer
d_integerSize_4 = size
-- Cost.Size.byteStringSize
d_byteStringSize_6 ::
  MAlonzo.Code.Utils.T_ByteString_386 -> Integer
d_byteStringSize_6 = size
-- Cost.Size.g1ElementSize
d_g1ElementSize_8 ::
  MAlonzo.Code.Utils.T_Bls12'45'381'45'G1'45'Element_670 -> Integer
d_g1ElementSize_8 = size
-- Cost.Size.g2ElementSize
d_g2ElementSize_10 ::
  MAlonzo.Code.Utils.T_Bls12'45'381'45'G2'45'Element_674 -> Integer
d_g2ElementSize_10 = size
-- Cost.Size.mlResultElementSize
d_mlResultElementSize_12 ::
  MAlonzo.Code.Utils.T_Bls12'45'381'45'MlResult_678 -> Integer
d_mlResultElementSize_12 = size
-- Cost.Size.dataSize
d_dataSize_14 :: MAlonzo.Code.Utils.T_DATA_524 -> Integer
d_dataSize_14 = size
-- Cost.Size.boolSize
d_boolSize_16 :: Bool -> Integer
d_boolSize_16 = size
-- Cost.Size.unitSize
d_unitSize_18 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 -> Integer
d_unitSize_18 = size
-- Cost.Size.stringSize
d_stringSize_20 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
d_stringSize_20 = size
-- Cost.Size.defaultConstantMeasure
d_defaultConstantMeasure_22 ::
  MAlonzo.Code.RawU.T_TmCon_202 -> Integer
d_defaultConstantMeasure_22 v0
  = case coe v0 of
      MAlonzo.Code.RawU.C_tmCon_206 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Builtin.Signature.C_atomic_12 v4
               -> case coe v4 of
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                      -> coe d_integerSize_4 v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBytestring_10
                      -> coe d_byteStringSize_6 v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aString_12
                      -> coe d_stringSize_20 v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14
                      -> coe d_unitSize_18 v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16
                      -> coe d_boolSize_16 v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                      -> coe d_dataSize_14 v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_20
                      -> coe d_g1ElementSize_8 v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_22
                      -> coe d_g2ElementSize_10 v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_24
                      -> coe d_mlResultElementSize_12 v2
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Builtin.Signature.C_list_16 v4
               -> coe MAlonzo.Code.Utils.du_length_424 (coe v2)
             MAlonzo.Code.Builtin.Signature.C_array_20 v4
               -> let v5
                        = coe MAlonzo.Code.Utils.d_HSlengthOfArray_512 erased v2 in
                  coe
                    (case coe v5 of
                       0 -> coe (1 :: Integer)
                       _ | coe geqInt (coe v5) (coe (1 :: Integer)) -> coe v5
                       _ -> coe (1 :: Integer))
             MAlonzo.Code.Builtin.Signature.C_pair_24 v4 v5
               -> coe seq (coe v2) (coe (1 :: Integer))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Size.defaultValueMeasure
d_defaultValueMeasure_78 ::
  MAlonzo.Code.Untyped.CEK.T_Value_14 -> Integer
d_defaultValueMeasure_78 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Untyped.CEK.C_V'45'con_50 v2 v3
           -> coe
                d_defaultConstantMeasure_22
                (coe MAlonzo.Code.RawU.C_tmCon_206 (coe v2) (coe v3))
         _ -> coe v1)
