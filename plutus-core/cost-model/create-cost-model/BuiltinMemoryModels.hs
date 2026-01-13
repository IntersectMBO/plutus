-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

{-| The memory models for the default set of builtins.  These are copied into
builtinCostModel.json by generate-cost-model. -}
module BuiltinMemoryModels (builtinMemoryModels, Id (..))
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

newtype Id a = Id {getId :: a}

{- Note [Memory model for Value builtins]
---------------------------------------

## Overview

The memory models for the Value builtins estimate the heap allocation
required for the resulting 'Value's. Memory usage is modeled as a function of the
number of unique (currency symbol, token name) pairs, based on worst-case allocation.

## Value Structure

Structurally, a 'Value' consists of:
  - A nested 'Data.Map.Map': Map CurrencySymbol (Map TokenName Integer)
  - Bookkeeping data: two unboxed 'Int's and a 'Data.IntMap.IntMap Int'

Based on the [ghc runtime memory layout](https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/storage/heap-objects),
we can model the top-level memory allocation for a 'Value' as:
  - 1 word for the 'Value' constructor
  - 1 word for each of the two unboxed 'Int's
  - 1 word for the pointer to the 'IntMap'
  - 1 word for the pointer to the nested 'Map'
  - The allocations for the 'IntMap' and nested 'Map' themselves

## Memory Analysis Assumptions

We assume for each builtin application:
  1. Both trees must be completely reallocated (worst-case)
  2. The map structure is flat, where each currency symbol maps to only one token name
  3. This simplifies analysis while providing a reasonable approximation
  4. Deeper trees would require more reallocation, but accounting for this is too complex

## Per-Pair Allocation (Outer and Inner Maps)

'Map' is implemented as a balanced binary tree (Data.Map.Internal):
@
  data Map k a  = Bin {-# UNPACK #-} !Int !k a !(Map k a) !(Map k a)
                | Tip
@

For each unique (currency symbol, token name) pair:

Outer 'Map' (CurrencySymbol to inner 'Map'):
  - 1 word for the 'Bin' closure
  - 1 word for the unboxed 'Int#'
  - 5 words for the 'CurrencySymbol' (pointer + bytestring; assume maxBound and unshared)
  - 1 word for pointer to the inner 'Map'
  - 1 word for pointer to first child 'Bin'
  - 1 word for pointer to second child 'Tip' (shared)

Inner 'Map' (TokenName to Integer):
  - 1 word for the 'Bin' closure
  - 5 words for the 'TokenName' (pointer + bytestring; assume maxBound and unshared)
  - 3 words for the 'Integer' (pointer + closure data; assume maxBound and unshared)

Shared structures (counted once across all pairs):
  - 1 word for the 'Tip' closure for outer 'Map'
  - 1 word for the 'Tip' closure for inner 'Map'

\**Total per pair: 21 words**

Note: Both 'CurrencySymbol' and 'TokenName' are newtypes wrapping 'ByteString'.

## Bookkeeping (IntMap) Allocation

The 'IntMap' contains exactly as many keys as there are unique inner map sizes.
In our worst-case flat scenario (all inner maps have size 1), the footprint is constant:
  - 1 word for the 'Tip' constructor
  - 2 words for key and value pointers
  - 2 words for key 'Int' closure (header + payload)
  - 2 words for value 'Int' closure (header + payload)

\**Total for IntMap: 7 words (constant)**

## Final formulas for calculating each builtin's memory usage

Combining per-pair and bookkeeping allocations:

    Memory = 21*n + 12

where 'n' is the number of unique (currency symbol, token name) pairs in the 'Value'.

This formula is used for the cost models of 'insertCoin', 'unionValue' and 'scaleValue'.

For 'insertCoin', the worst-case allocation occurs when a new pair is inserted into the map.
Given the balanced tree representation, the memory allocation is based on 'ValueMaxDepth'
which calculates the logarithmic depth of the tree. Thus, for 'insertCoin':

    Memory = 21*log(n) + 12 + 21 + 12 = 21*log(n) + 45

For 'unionValue', worst-case assumes disjoint sets of pairs in both 'Value's being united:

    Memory = 21*n + 12 + 21*m + 12 = 21*(n + m) + 24
  where 'n' and 'm' are the total sizes of each input 'Value'.

For 'scaleValue', since every quantity in the 'Value' is modified, a new 'Value' of the same
size must be allocated:

    Memory = 21*n + 12

where 'n' is the total size of the input 'Value'.

## Costing 'valueData' and 'unValueData'

Since 'valueData' and 'unValueData' convert between 'Value' and 'Data', we need to estimate
the memory allocation for 'Data' as well, and how it relates to the size of the 'Value'.

The definition of 'Data' is as follows:
@
  data Data
    = Constr Integer [Data]
    | Map [(Data, Data)]
    | List [Data]
    | I Integer
    | B BS.ByteString
@

Since we're interested only in well-formed 'Value's, we can focus on just the subset of constructors
which are used in the 'Data' representation of 'Value's:
  - 'Map' for the outer and inner maps
  - 'I' for the integer quantities
  - 'B' for the currency symbols and token names

The cost of 'valueData' is given by the memory allocation of the resulting 'Data' structure, as a function
of the number of unique (currency symbol, token name) pairs in the 'Value'.

Let's analyze the memory allocation for 'Data' representing a 'Value' with 'n' unique pairs:
  1. If n = 0, the 'Data' representation is 'Map []' which allocates 1 word for the 'Map' constructor plus
    one pointer to the shared empty list CAF, in total 2 words.
  2. For n > 0, the memory allocation depends on the structure of the nested 'Map's in 'Data'; based on simple
  experiments, we find that the overhead is higher for a flat structure compared to a deeply nested one. Given that
  we're interested in worst-case allocation, we assume a flat structure where each currency symbol maps to only one token name.

Calculating the memory allocation for 'Data' in the flat structure:
  - Outer 'Map' with 'n' entries:
    - 1 word for the 'Map' closure
    - For each of the 'n > 0' entries:
      - 1 word for the ':' closure
      - 1 word for the pair closure
      - 1 word for the 'B' closure + 5 words for the bytestring itself
      - Inner 'Map' with 1 entry (for each currency symbol):
        - 1 word for the 'Map' closure
        - 1 word for the ':' closure
        - 1 word for the pair closure
        - 1 word for the 'B' closure + 5 words for the bytestring itself
        - 1 word for the 'I' closure + 3 words for the integer itself
        - 1 word for the pointer to the empty list CAF
    - 1 word for the pointer to the empty list CAF

Thus, the memory model for 'valueData' is:

    Memory = 22*n + 2

where 'n' is the number of unique (currency symbol, token name) pairs in the 'Value'.

For 'unValueData' we need to estimate the memory allocation for the resulting 'Value',
based on the size of the input 'Data'. This size is defined as the number of 'Data' nodes
in the structure, calculated using the 'DataNodeCount' instance of 'ExMemoryUsage'.

A tricky part is that multiple different 'Data' structures may represent the same 'Value'.
We need to estimate the worst-case memory allocation for 'Value' based on the number of 'Data' nodes,
which translates to estimating the maximum number of unique (currency symbol, token name) pairs
from a given number of 'Data' nodes.
By running some simple experiments, we can observe that we can fit more unique pairs in a nested
structure, where the outer 'Map' contains a single currency symbol mapping to an inner 'Map' with
multiple token names.

By computing the number of 'Data' nodes for nested structures with increasing number of unique pairs,
we obtain the following mapping:
@
  1 -> empty Val
  5 -> Val with 1 elem
  7 -> Val with 2 elem
  9 -> Val with 3 elem
  11 -> Val with 4 elem
  ...
  n -> Val with (n - 3)/ 2 elems
@
From this we can derive that the memory allocated for the resulting 'Value' is:

    Memory = 21*((n - 3)/2) + 12 = 10.5*n - 19.5 --approx--> 11*n - 19

where 'n' is the number of 'Data' nodes in the input structure.

However, this formula can yield negative results for small 'n' (specifically n < 4).
Due to limitations in our costing framework, we cannot case on the value of 'n' to handle
such situations. To ensure non-negative memory costs, we further overapproximate the formula
to remove the negative intercept:

    Memory = 21*(n/2) + 12 = 10.5*n + 12 --approx--> 11*n + 12
where 'n' is the number of 'Data' nodes in the input structure.

-}

builtinMemoryModels :: BuiltinCostModelBase Id
builtinMemoryModels =
  BuiltinCostModelBase
    { paramAddInteger = Id $ ModelTwoArgumentsMaxSize $ OneVariableLinearFunction 1 1
    , paramSubtractInteger = Id $ ModelTwoArgumentsMaxSize $ OneVariableLinearFunction 1 1
    , paramMultiplyInteger = Id $ ModelTwoArgumentsAddedSizes $ identityFunction
    , paramDivideInteger = Id $ ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
    , paramQuotientInteger = Id $ ModelTwoArgumentsSubtractedSizes $ ModelSubtractedSizes 0 1 1
    , paramRemainderInteger = Id $ ModelTwoArgumentsLinearInY $ identityFunction
    , paramModInteger = Id $ ModelTwoArgumentsLinearInY $ identityFunction
    , paramEqualsInteger = Id $ boolMemModel
    , paramLessThanInteger = Id $ boolMemModel
    , paramLessThanEqualsInteger = Id $ boolMemModel
    , paramAppendByteString = Id $ ModelTwoArgumentsAddedSizes $ identityFunction
    , paramConsByteString = Id $ ModelTwoArgumentsAddedSizes $ identityFunction
    , -- sliceByteString doesn't actually allocate a new bytestring: it creates an
      -- object containing a pointer into the original, together with a length.
      paramSliceByteString = Id $ ModelThreeArgumentsLinearInZ $ OneVariableLinearFunction 4 0
    , paramLengthOfByteString = Id $ ModelOneArgumentConstantCost 10
    , paramIndexByteString = Id $ ModelTwoArgumentsConstantCost 4
    , paramEqualsByteString = Id $ boolMemModel
    , paramLessThanByteString = Id $ boolMemModel
    , paramLessThanEqualsByteString = Id $ boolMemModel
    , paramSha2_256 = Id $ hashMemModel Hash.sha2_256
    , paramSha3_256 = Id $ hashMemModel Hash.sha3_256
    , paramBlake2b_256 = Id $ hashMemModel Hash.blake2b_256
    , paramVerifyEd25519Signature = Id $ ModelThreeArgumentsConstantCost 10
    , paramVerifyEcdsaSecp256k1Signature = Id $ ModelThreeArgumentsConstantCost 10
    , paramVerifySchnorrSecp256k1Signature = Id $ ModelThreeArgumentsConstantCost 10
    , paramAppendString = Id $ ModelTwoArgumentsAddedSizes $ OneVariableLinearFunction 4 1
    , paramEqualsString = Id $ boolMemModel
    , -- In the worst case two UTF-16 bytes encode to three UTF-8 bytes, so two
      -- output words per input word should cover that.
      paramEncodeUtf8 = Id $ ModelOneArgumentLinearInX $ OneVariableLinearFunction 4 2
    , -- In the worst case one UTF-8 byte decodes to two UTF-16 bytes
      paramDecodeUtf8 = Id $ ModelOneArgumentLinearInX $ OneVariableLinearFunction 4 2
    , paramIfThenElse = Id $ ModelThreeArgumentsConstantCost 1
    , paramChooseUnit = Id $ ModelTwoArgumentsConstantCost 4
    , paramTrace = Id $ ModelTwoArgumentsConstantCost 32
    , paramFstPair = Id $ ModelOneArgumentConstantCost 32
    , paramSndPair = Id $ ModelOneArgumentConstantCost 32
    , paramChooseList = Id $ ModelThreeArgumentsConstantCost 32
    , paramMkCons = Id $ ModelTwoArgumentsConstantCost 32
    , paramHeadList = Id $ ModelOneArgumentConstantCost 32
    , paramTailList = Id $ ModelOneArgumentConstantCost 32
    , paramNullList = Id $ ModelOneArgumentConstantCost 32
    , paramChooseData = Id $ ModelSixArgumentsConstantCost 32
    , paramConstrData = Id $ ModelTwoArgumentsConstantCost 32
    , paramMapData = Id $ ModelOneArgumentConstantCost 32
    , paramListData = Id $ ModelOneArgumentConstantCost 32
    , paramIData = Id $ ModelOneArgumentConstantCost 32
    , paramBData = Id $ ModelOneArgumentConstantCost 32
    , paramUnConstrData = Id $ ModelOneArgumentConstantCost 32
    , paramUnMapData = Id $ ModelOneArgumentConstantCost 32
    , paramUnListData = Id $ ModelOneArgumentConstantCost 32
    , paramUnIData = Id $ ModelOneArgumentConstantCost 32
    , paramUnBData = Id $ ModelOneArgumentConstantCost 32
    , paramEqualsData = Id $ ModelTwoArgumentsConstantCost 1
    , paramMkPairData = Id $ ModelTwoArgumentsConstantCost 32
    , paramMkNilData = Id $ ModelOneArgumentConstantCost 32
    , paramMkNilPairData = Id $ ModelOneArgumentConstantCost 32
    , paramSerialiseData = Id $ ModelOneArgumentLinearInX $ OneVariableLinearFunction 0 2
    , paramBls12_381_G1_add = Id $ ModelTwoArgumentsConstantCost g1MemSize
    , paramBls12_381_G1_neg = Id $ ModelOneArgumentConstantCost g1MemSize
    , paramBls12_381_G1_scalarMul = Id $ ModelTwoArgumentsConstantCost g1MemSize
    , paramBls12_381_G1_multiScalarMul = Id $ ModelTwoArgumentsConstantCost g1MemSize
    , paramBls12_381_G1_equal = Id $ boolMemModel
    , paramBls12_381_G1_compress = Id $ ModelOneArgumentConstantCost g1CompressedSize
    , paramBls12_381_G1_uncompress = Id $ ModelOneArgumentConstantCost g1MemSize
    , paramBls12_381_G1_hashToGroup = Id $ ModelTwoArgumentsConstantCost g1MemSize
    , paramBls12_381_G2_add = Id $ ModelTwoArgumentsConstantCost g2MemSize
    , paramBls12_381_G2_neg = Id $ ModelOneArgumentConstantCost g2MemSize
    , paramBls12_381_G2_scalarMul = Id $ ModelTwoArgumentsConstantCost g2MemSize
    , paramBls12_381_G2_multiScalarMul = Id $ ModelTwoArgumentsConstantCost g2MemSize
    , paramBls12_381_G2_equal = Id $ boolMemModel
    , paramBls12_381_G2_compress = Id $ ModelOneArgumentConstantCost g2CompressedSize
    , paramBls12_381_G2_uncompress = Id $ ModelOneArgumentConstantCost g2MemSize
    , paramBls12_381_G2_hashToGroup = Id $ ModelTwoArgumentsConstantCost g2MemSize
    , paramBls12_381_millerLoop = Id $ ModelTwoArgumentsConstantCost mlResultMemSize
    , paramBls12_381_mulMlResult = Id $ ModelTwoArgumentsConstantCost mlResultMemSize
    , paramBls12_381_finalVerify = Id $ boolMemModel
    , paramBlake2b_224 = Id $ hashMemModel Hash.blake2b_224
    , paramKeccak_256 = Id $ hashMemModel Hash.keccak_256
    , -- integerToByteString e w n allocates a bytestring of length w if w is
      -- nonzero and a bytestring just big enough to contain n otherwise, so we need
      -- a special memory costing function to handle that.
      paramIntegerToByteString = Id $ ModelThreeArgumentsLiteralInYOrLinearInZ identityFunction
    , paramByteStringToInteger = Id $ ModelTwoArgumentsLinearInY identityFunction
    , -- andByteString b y z etc. return something whose length is min(length(y),length(z)) if b is
      -- False, max (...) otherwise.  For the time being we conservatively assume max in all cases.
      paramAndByteString = Id $ ModelThreeArgumentsLinearInMaxYZ identityFunction
    , paramOrByteString = Id $ ModelThreeArgumentsLinearInMaxYZ identityFunction
    , paramXorByteString = Id $ ModelThreeArgumentsLinearInMaxYZ identityFunction
    , paramComplementByteString = Id $ ModelOneArgumentLinearInX identityFunction
    , paramReadBit = Id $ ModelTwoArgumentsConstantCost 1
    , paramWriteBits = Id $ ModelThreeArgumentsLinearInX identityFunction
    , -- The empty bytestring has memory usage 1, so we add an extra memory unit here to make sure that
      -- the memory cost of `replicateByte` is always nonzero. That means that we're charging one unit
      -- more than we perhaps should for nonempty bytestrings, but that's negligible (plus there's some
      -- overhead for bytesrings anyway).  Note also that `replicateByte`'s argument is costed as a
      -- literal size.
      paramReplicateByte = Id $ ModelTwoArgumentsLinearInX $ OneVariableLinearFunction 1 1
    , paramShiftByteString = Id $ ModelTwoArgumentsLinearInX identityFunction
    , paramRotateByteString = Id $ ModelTwoArgumentsLinearInX identityFunction
    , paramCountSetBits = Id $ ModelOneArgumentConstantCost 1
    , paramFindFirstSetBit = Id $ ModelOneArgumentConstantCost 1
    , paramRipemd_160 = Id $ hashMemModel Hash.ripemd_160
    , paramExpModInteger = Id $ ModelThreeArgumentsLinearInZ identityFunction
    , paramDropList = Id $ ModelTwoArgumentsConstantCost 4
    , paramLengthOfArray = Id $ ModelOneArgumentConstantCost 10
    , paramListToArray = Id $ ModelOneArgumentLinearInX $ OneVariableLinearFunction 7 1
    , paramIndexArray = Id $ ModelTwoArgumentsConstantCost 32
    , -- Builtin values
      paramLookupCoin = Id $ ModelThreeArgumentsConstantCost 10
    , paramValueContains = Id $ ModelTwoArgumentsConstantCost 32
    , -- See Note [Memory model for Value builtins]
      paramValueData = Id $ ModelOneArgumentLinearInX $ OneVariableLinearFunction 2 22
    , -- See Note [Memory model for Value builtins]
      paramUnValueData = Id $ ModelOneArgumentLinearInX $ OneVariableLinearFunction 12 11
    , -- See Note [Memory model for Value builtins]
      paramInsertCoin = Id $ ModelFourArgumentsLinearInU $ OneVariableLinearFunction 45 21
    , -- See Note [Memory model for Value builtins]
      paramUnionValue = Id $ ModelTwoArgumentsAddedSizes $ OneVariableLinearFunction 24 21
    , -- See Note [Memory model for Value builtins]
      paramScaleValue = Id $ ModelTwoArgumentsLinearInY $ OneVariableLinearFunction 12 21
    }
  where
    identityFunction = OneVariableLinearFunction 0 1
