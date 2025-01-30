-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

-- | The memory models for the default set of builtins.  These are copied into
-- builtinCostModel.json by generate-cost-model.

module BuiltinMemoryModels (builtinMemoryModels, Id(..))
where

import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as Pairing
import PlutusCore.Crypto.Hash qualified as Hash
import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.CostStream
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.ExMemoryUsage

import Data.ByteString (ByteString)
import Data.Coerce (coerce)

-- Some utilities for calculating memory sizes.

boolMemModel :: ModelTwoArguments
boolMemModel = ModelTwoArgumentsConstantCost 1

memoryUsageAsCostingInteger :: ExMemoryUsage a => a -> CostingInteger
memoryUsageAsCostingInteger = coerce . sumCostStream . flattenCostRose . memoryUsage

hashMemModel :: (ByteString -> ByteString) -> ModelOneArgument
hashMemModel f = ModelOneArgumentConstantCost $ memoryUsageAsCostingInteger $ f ""

toMemSize :: Int -> CostingInteger
toMemSize n = fromIntegral $ n `div` 8

-- Group order is 255 bits -> 32 bytes (4 words).
-- Field size is 381 bits  -> 48 bytes (6 words)
-- (with three spare bits used for encoding purposes).

-- Sizes below from sizePoint, compressedSizePoint, and sizePT in
-- Crypto.EllipticCurve.BLS12_381.Internal

-- In-memory G1 points take up 144 bytes (18 words).
-- These are projective points, so we have *three* 48-byte coordinates.
g1MemSize :: CostingInteger
g1MemSize = toMemSize G1.memSizeBytes

-- Compressed G1 points take up 48 bytes (6 words)
g1CompressedSize :: CostingInteger
g1CompressedSize = toMemSize G1.compressedSizeBytes

-- In-memory G2 points take up 288 bytes (36 words)
g2MemSize :: CostingInteger
g2MemSize = toMemSize G2.memSizeBytes

-- Compressed G2 points take up 96 bytes (12 words)
g2CompressedSize :: CostingInteger
g2CompressedSize = toMemSize G2.compressedSizeBytes

-- In-memory G2 points take up 576 bytes (72 words)
mlResultMemSize :: CostingInteger
mlResultMemSize = toMemSize Pairing.mlResultMemSizeBytes

-- The memory models for the default builtins

newtype Id a = Id { getId :: a }

builtinMemoryModels :: BuiltinCostModelBase Id
builtinMemoryModels = BuiltinCostModelBase
  { paramAddInteger                      = Id $ ModelTwoArgumentsMaxSize $ OneVariableLinearFunction 1 1
  , paramSubtractInteger                 = Id $ ModelTwoArgumentsMaxSize $ OneVariableLinearFunction 1 1
  , paramMultiplyInteger                 = Id $ ModelTwoArgumentsAddedSizes $ identityFunction
  , paramDivideInteger                   = Id $ ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
  , paramQuotientInteger                 = Id $ ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
  , paramRemainderInteger                = Id $ ModelTwoArgumentsLinearInY $ identityFunction
  , paramModInteger                      = Id $ ModelTwoArgumentsLinearInY $ identityFunction
  , paramEqualsInteger                   = Id $ boolMemModel
  , paramLessThanInteger                 = Id $ boolMemModel
  , paramLessThanEqualsInteger           = Id $ boolMemModel
  , paramAppendByteString                = Id $ ModelTwoArgumentsAddedSizes $ identityFunction
  , paramConsByteString                  = Id $ ModelTwoArgumentsAddedSizes $ identityFunction
    -- sliceByteString doesn't actually allocate a new bytestring: it creates an
    -- object containing a pointer into the original, together with a length.
  , paramSliceByteString                 = Id $ ModelThreeArgumentsLinearInZ $ OneVariableLinearFunction 4 0
  , paramLengthOfByteString              = Id $ ModelOneArgumentConstantCost 10
  , paramIndexByteString                 = Id $ ModelTwoArgumentsConstantCost 4
  , paramEqualsByteString                = Id $ boolMemModel
  , paramLessThanByteString              = Id $ boolMemModel
  , paramLessThanEqualsByteString        = Id $ boolMemModel
  , paramSha2_256                        = Id $ hashMemModel Hash.sha2_256
  , paramSha3_256                        = Id $ hashMemModel Hash.sha3_256
  , paramBlake2b_256                     = Id $ hashMemModel Hash.blake2b_256
  , paramVerifyEd25519Signature          = Id $ ModelThreeArgumentsConstantCost 10
  , paramVerifyEcdsaSecp256k1Signature   = Id $ ModelThreeArgumentsConstantCost 10
  , paramVerifySchnorrSecp256k1Signature = Id $ ModelThreeArgumentsConstantCost 10
  , paramAppendString                    = Id $ ModelTwoArgumentsAddedSizes $ OneVariableLinearFunction 4 1
  , paramEqualsString                    = Id $ boolMemModel
  -- In the worst case two UTF-16 bytes encode to three UTF-8 bytes, so two
  -- output words per input word should cover that.
  , paramEncodeUtf8                      = Id $ ModelOneArgumentLinearInX $ OneVariableLinearFunction 4 2
  -- In the worst case one UTF-8 byte decodes to two UTF-16 bytes
  , paramDecodeUtf8                      = Id $ ModelOneArgumentLinearInX $ OneVariableLinearFunction 4 2
  , paramIfThenElse                      = Id $ ModelThreeArgumentsConstantCost  1
  , paramChooseUnit                      = Id $ ModelTwoArgumentsConstantCost    4
  , paramTrace                           = Id $ ModelTwoArgumentsConstantCost   32
  , paramFstPair                         = Id $ ModelOneArgumentConstantCost    32
  , paramSndPair                         = Id $ ModelOneArgumentConstantCost    32
  , paramChooseList                      = Id $ ModelThreeArgumentsConstantCost 32
  , paramMkCons                          = Id $ ModelTwoArgumentsConstantCost   32
  , paramHeadList                        = Id $ ModelOneArgumentConstantCost    32
  , paramTailList                        = Id $ ModelOneArgumentConstantCost    32
  , paramNullList                        = Id $ ModelOneArgumentConstantCost    32
  , paramDropList                      = Id $ ModelOneArgumentConstantCost    32
  , paramIntegerToByteString             = Id $ ModelThreeArgumentsLiteralInYOrLinearInZ identityFunction
  , paramByteStringToInteger             = Id $ ModelTwoArgumentsLinearInY identityFunction
  -- andByteString b y z etc. return something whose length is min(length(y),length(z)) if b is
  -- False, max (...) otherwise.  For the time being we conservatively assume max in all cases.
  , paramAndByteString                   = Id $ ModelThreeArgumentsLinearInMaxYZ identityFunction
  , paramOrByteString                    = Id $ ModelThreeArgumentsLinearInMaxYZ identityFunction
  , paramXorByteString                   = Id $ ModelThreeArgumentsLinearInMaxYZ identityFunction
  , paramComplementByteString            = Id $ ModelOneArgumentLinearInX identityFunction
  , paramReadBit                         = Id $ ModelTwoArgumentsConstantCost 1
  , paramWriteBits                       = Id $ ModelThreeArgumentsLinearInX identityFunction
  -- The empty bytestring has memory usage 1, so we add an extra memory unit here to make sure that
  -- the memory cost of `replicateByte` is always nonzero. That means that we're charging one unit
  -- ore than we perhaps should for nonempty bytestrings, but that's negligible (plus there's some
  -- overhead for bytesrings anyway).  Note also that `replicateByte`'s argument is costed as a
  -- literal size.
  , paramReplicateByte                   = Id $ ModelTwoArgumentsLinearInX $ OneVariableLinearFunction 1 1
  , paramShiftByteString                 = Id $ ModelTwoArgumentsLinearInX identityFunction
  , paramRotateByteString                = Id $ ModelTwoArgumentsLinearInX identityFunction
  , paramCountSetBits                    = Id $ ModelOneArgumentConstantCost 1
  , paramFindFirstSetBit                 = Id $ ModelOneArgumentConstantCost 1
  , paramRipemd_160                      = Id $ hashMemModel Hash.ripemd_160
  , paramExpModInteger                   = Id $ ModelThreeArgumentsConstantCost 100000000000 -- FIXME: stub
  }
  where identityFunction = OneVariableLinearFunction 0 1
