{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Evaluation.Builtins.BLS12_381.Utils
where

import Evaluation.Builtins.Common

import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModel)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusPrelude (def)
import UntypedPlutusCore qualified as UPLC

import Data.Bits (complement, xor, (.&.), (.|.))
import Data.ByteString as BS (ByteString, cons, uncons)
import Data.Word (Word8)

-- PLC utilities

-- Evaluating PLC terms

type PlcTerm = PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ()
type PlcError = PLC.Error PLC.DefaultUni PLC.DefaultFun ()
type UplcTerm = UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ()

data CekResult =
    TypeCheckError PlcError
  | CekError
  | CekSuccess UplcTerm
    deriving stock (Eq, Show)

evalTerm :: PlcTerm -> CekResult
evalTerm term =
    case typecheckEvaluateCekNoEmit def defaultBuiltinCostModel term
    of Left e -> TypeCheckError e
       Right x  ->
           case x of
             PLC.EvaluationFailure   -> CekError
             PLC.EvaluationSuccess s -> CekSuccess s

-- Constructing PLC constants and applications

uplcTrue :: CekResult
uplcTrue = CekSuccess $ mkConstant () True

uplcFalse :: CekResult
uplcFalse = CekSuccess $ mkConstant () False

integer :: Integer -> PlcTerm
integer = mkConstant ()

bytestring :: ByteString -> PlcTerm
bytestring = mkConstant ()

mkApp1 :: PLC.DefaultFun -> PlcTerm -> PlcTerm
mkApp1 b x = mkIterAppNoAnn (builtin () b) [x]

mkApp2 :: PLC.DefaultFun -> PlcTerm -> PlcTerm -> PlcTerm
mkApp2 b x y = mkIterAppNoAnn (builtin () b) [x,y]

{- | ByteString utilities.  These are used in tests to check that the format of
   compressed points conforms to the specification at
   https://github.com/supranational/blst#serialization-format . -}

-- The most signiificant bit of a serialised curve point is set if the
-- serialised point is in compressed form (x-coordinate only)
compressionBit :: Word8
compressionBit = 0x80

-- The second most significant bit is set if and only if the point is the point
-- at infinity (the zero of the group); if it is set, all other bits should be zero.
infinityBit :: Word8
infinityBit = 0x40

-- The third most significant bit of a compressed point denotes the "sign" of
-- the y-coordinate of the associated point: it is set if and only if the point
-- is not the point at infinity and the y-coordinate is the lexicographically
-- larger one with the given x coordinate.
signBit :: Word8
signBit = 0x20

unsafeUnconsBS :: ByteString -> (Word8, ByteString)
unsafeUnconsBS b =
    case BS.uncons b of
      Nothing -> error "Tried to uncons empty bytestring"
      Just p  -> p

-- | Apply some function to the most significant byte of a bytestring
modifyMSB :: (Word8 -> Word8) -> ByteString -> ByteString
modifyMSB f s =
    let (w,rest) = unsafeUnconsBS s
    in BS.cons (f w) rest

-- | Flip a specified set of bits in the most significant byte of a bytestring.
flipBits :: Word8 -> ByteString -> ByteString
flipBits mask = modifyMSB (mask `xor`)

-- | Clear a specified set of bits in the most significant byte of a bytestring.
clearBits :: Word8 -> ByteString -> ByteString
clearBits mask = modifyMSB ((complement mask) .&.)

-- | Set a specified set of bits in the most significant byte of a bytestring.
setBits :: Word8 -> ByteString -> ByteString
setBits mask = modifyMSB (mask .|.)

-- | Check that a specified set of bits is set in the most significant byte of a
-- bytestring.
isSet :: Word8 -> ByteString -> Bool
isSet mask s =
    let (w,_) = unsafeUnconsBS s
    in w .&. mask == mask
