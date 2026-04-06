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

module MAlonzo.Code.Agda.Builtin.Float where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.RTE.Float

-- Agda.Builtin.Float.Float
type T_Float_6 = Double
d_Float_6
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Builtin.Float.Float"
-- Agda.Builtin.Float.primFloatInequality
d_primFloatInequality_8 = MAlonzo.RTE.Float.doubleLe
-- Agda.Builtin.Float.primFloatEquality
d_primFloatEquality_10 = MAlonzo.RTE.Float.doubleEq
-- Agda.Builtin.Float.primFloatLess
d_primFloatLess_12 = MAlonzo.RTE.Float.doubleLt
-- Agda.Builtin.Float.primFloatIsInfinite
d_primFloatIsInfinite_14 = (isInfinite :: Double -> Bool)
-- Agda.Builtin.Float.primFloatIsNaN
d_primFloatIsNaN_16 = (isNaN :: Double -> Bool)
-- Agda.Builtin.Float.primFloatIsNegativeZero
d_primFloatIsNegativeZero_18 = (isNegativeZero :: Double -> Bool)
-- Agda.Builtin.Float.primFloatIsSafeInteger
d_primFloatIsSafeInteger_20 = MAlonzo.RTE.Float.isSafeInteger
-- Agda.Builtin.Float.primFloatToWord64
d_primFloatToWord64_22 = MAlonzo.RTE.Float.doubleToWord64
-- Agda.Builtin.Float.primNatToFloat
d_primNatToFloat_24
  = (MAlonzo.RTE.Float.intToDouble :: Integer -> Double)
-- Agda.Builtin.Float.primIntToFloat
d_primIntToFloat_26
  = (MAlonzo.RTE.Float.intToDouble :: Integer -> Double)
-- Agda.Builtin.Float.primFloatRound
d_primFloatRound_28 = MAlonzo.RTE.Float.doubleRound
-- Agda.Builtin.Float.primFloatFloor
d_primFloatFloor_30 = MAlonzo.RTE.Float.doubleFloor
-- Agda.Builtin.Float.primFloatCeiling
d_primFloatCeiling_32 = MAlonzo.RTE.Float.doubleCeiling
-- Agda.Builtin.Float.primFloatToRatio
d_primFloatToRatio_36 = MAlonzo.RTE.Float.doubleToRatio
-- Agda.Builtin.Float.primRatioToFloat
d_primRatioToFloat_38 = MAlonzo.RTE.Float.ratioToDouble
-- Agda.Builtin.Float.primFloatDecode
d_primFloatDecode_42 = MAlonzo.RTE.Float.doubleDecode
-- Agda.Builtin.Float.primFloatEncode
d_primFloatEncode_44 = MAlonzo.RTE.Float.doubleEncode
-- Agda.Builtin.Float.primShowFloat
d_primShowFloat_46
  = (Data.Text.pack . show :: Double -> Data.Text.Text)
-- Agda.Builtin.Float.primFloatPlus
d_primFloatPlus_48 = MAlonzo.RTE.Float.doublePlus
-- Agda.Builtin.Float.primFloatMinus
d_primFloatMinus_50 = MAlonzo.RTE.Float.doubleMinus
-- Agda.Builtin.Float.primFloatTimes
d_primFloatTimes_52 = MAlonzo.RTE.Float.doubleTimes
-- Agda.Builtin.Float.primFloatDiv
d_primFloatDiv_54 = MAlonzo.RTE.Float.doubleDiv
-- Agda.Builtin.Float.primFloatPow
d_primFloatPow_56 = MAlonzo.RTE.Float.doublePow
-- Agda.Builtin.Float.primFloatNegate
d_primFloatNegate_58 = MAlonzo.RTE.Float.doubleNegate
-- Agda.Builtin.Float.primFloatSqrt
d_primFloatSqrt_60 = MAlonzo.RTE.Float.doubleSqrt
-- Agda.Builtin.Float.primFloatExp
d_primFloatExp_62 = MAlonzo.RTE.Float.doubleExp
-- Agda.Builtin.Float.primFloatLog
d_primFloatLog_64 = MAlonzo.RTE.Float.doubleLog
-- Agda.Builtin.Float.primFloatSin
d_primFloatSin_66 = MAlonzo.RTE.Float.doubleSin
-- Agda.Builtin.Float.primFloatCos
d_primFloatCos_68 = MAlonzo.RTE.Float.doubleCos
-- Agda.Builtin.Float.primFloatTan
d_primFloatTan_70 = MAlonzo.RTE.Float.doubleTan
-- Agda.Builtin.Float.primFloatASin
d_primFloatASin_72 = MAlonzo.RTE.Float.doubleASin
-- Agda.Builtin.Float.primFloatACos
d_primFloatACos_74 = MAlonzo.RTE.Float.doubleACos
-- Agda.Builtin.Float.primFloatATan
d_primFloatATan_76 = MAlonzo.RTE.Float.doubleATan
-- Agda.Builtin.Float.primFloatATan2
d_primFloatATan2_78 = MAlonzo.RTE.Float.doubleATan2
-- Agda.Builtin.Float.primFloatSinh
d_primFloatSinh_80 = MAlonzo.RTE.Float.doubleSinh
-- Agda.Builtin.Float.primFloatCosh
d_primFloatCosh_82 = MAlonzo.RTE.Float.doubleCosh
-- Agda.Builtin.Float.primFloatTanh
d_primFloatTanh_84 = MAlonzo.RTE.Float.doubleTanh
-- Agda.Builtin.Float.primFloatASinh
d_primFloatASinh_86 = MAlonzo.RTE.Float.doubleASinh
-- Agda.Builtin.Float.primFloatACosh
d_primFloatACosh_88 = MAlonzo.RTE.Float.doubleACosh
-- Agda.Builtin.Float.primFloatATanh
d_primFloatATanh_90 = MAlonzo.RTE.Float.doubleATanh
-- Agda.Builtin.Float.primFloatNumericalEquality
d_primFloatNumericalEquality_92 :: T_Float_6 -> T_Float_6 -> Bool
d_primFloatNumericalEquality_92 = coe d_primFloatEquality_10
-- Agda.Builtin.Float.primFloatNumericalLess
d_primFloatNumericalLess_94 :: T_Float_6 -> T_Float_6 -> Bool
d_primFloatNumericalLess_94 = coe d_primFloatLess_12
-- Agda.Builtin.Float.primRound
d_primRound_96 :: T_Float_6 -> Maybe Integer
d_primRound_96 = coe d_primFloatRound_28
-- Agda.Builtin.Float.primFloor
d_primFloor_98 :: T_Float_6 -> Maybe Integer
d_primFloor_98 = coe d_primFloatFloor_30
-- Agda.Builtin.Float.primCeiling
d_primCeiling_100 :: T_Float_6 -> Maybe Integer
d_primCeiling_100 = coe d_primFloatCeiling_32
-- Agda.Builtin.Float.primExp
d_primExp_102 :: T_Float_6 -> T_Float_6
d_primExp_102 = coe d_primFloatExp_62
-- Agda.Builtin.Float.primLog
d_primLog_104 :: T_Float_6 -> T_Float_6
d_primLog_104 = coe d_primFloatLog_64
-- Agda.Builtin.Float.primSin
d_primSin_106 :: T_Float_6 -> T_Float_6
d_primSin_106 = coe d_primFloatSin_66
-- Agda.Builtin.Float.primCos
d_primCos_108 :: T_Float_6 -> T_Float_6
d_primCos_108 = coe d_primFloatCos_68
-- Agda.Builtin.Float.primTan
d_primTan_110 :: T_Float_6 -> T_Float_6
d_primTan_110 = coe d_primFloatTan_70
-- Agda.Builtin.Float.primASin
d_primASin_112 :: T_Float_6 -> T_Float_6
d_primASin_112 = coe d_primFloatASin_72
-- Agda.Builtin.Float.primACos
d_primACos_114 :: T_Float_6 -> T_Float_6
d_primACos_114 = coe d_primFloatACos_74
-- Agda.Builtin.Float.primATan
d_primATan_116 :: T_Float_6 -> T_Float_6
d_primATan_116 = coe d_primFloatATan_76
-- Agda.Builtin.Float.primATan2
d_primATan2_118 :: T_Float_6 -> T_Float_6 -> T_Float_6
d_primATan2_118 = coe d_primFloatATan2_78
