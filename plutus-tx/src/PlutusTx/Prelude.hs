-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
-- this module does lots of weird stuff deliberately
{- HLINT ignore -}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fmax-simplifier-iterations=0 #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

{-| The PlutusTx Prelude is a replacement for the Haskell Prelude that works
better with Plutus Tx. You should use it if you're writing code that
will be compiled with the Plutus Tx compiler.

@
    :set -XNoImplicitPrelude
    import PlutusTx.Prelude
@
-}
module PlutusTx.Prelude (
  -- * Classes
  module Eq,
  module Enum,
  module Ord,
  module Semigroup,
  module Monoid,
  module Numeric,
  module Function,
  module Functor,
  module Applicative,
  module Lattice,

  -- * Monad
  (Haskell.>>=),
  (Haskell.=<<),
  (Haskell.>>),
  Haskell.return,

  -- * Standard functions, Tuples
  module Base,

  -- * Tracing functions
  module Trace,

  -- * Unit
  BI.BuiltinUnit,

  -- * String
  BuiltinString,
  appendString,
  emptyString,
  equalsString,
  encodeUtf8,

  -- * Error
  error,
  check,

  -- * Booleans
  module Bool,

  -- * Integer numbers
  Integer,
  divide,
  modulo,
  quotient,
  remainder,
  even,
  odd,
  expMod,

  -- * Maybe
  module Maybe,

  -- * Either
  module Either,

  -- * ByteStrings
  BuiltinByteString,
  appendByteString,
  consByteString,
  takeByteString,
  dropByteString,
  sliceByteString,
  lengthOfByteString,
  indexByteString,
  emptyByteString,
  decodeUtf8,
  BuiltinByteStringUtf8 (..),
  Builtins.andByteString,
  Builtins.orByteString,
  Builtins.xorByteString,
  Builtins.complementByteString,

  -- ** Bit operations
  Builtins.readBit,
  Builtins.writeBits,
  Builtins.replicateByte,
  Builtins.shiftByteString,
  Builtins.rotateByteString,
  Builtins.countSetBits,
  Builtins.findFirstSetBit,

  -- * Hashes and Signatures
  sha2_256,
  sha3_256,
  blake2b_224,
  blake2b_256,
  keccak_256,
  ripemd_160,
  verifyEd25519Signature,
  verifyEcdsaSecp256k1Signature,
  verifySchnorrSecp256k1Signature,

  -- * Rational numbers
  Rational,
  unsafeRatio,
  ratio,
  fromInteger,
  round,

  -- * Other builtin Types
  BuiltinData,
  BI.BuiltinList,
  BI.BuiltinPair,

  -- * To/from Data
  ToData (..),
  FromData (..),
  UnsafeFromData (..),

  -- * BLS12_381
  BuiltinBLS12_381_G1_Element,
  bls12_381_G1_equals,
  bls12_381_G1_add,
  bls12_381_G1_neg,
  bls12_381_G1_scalarMul,
  bls12_381_G1_compress,
  bls12_381_G1_uncompress,
  bls12_381_G1_hashToGroup,
  bls12_381_G1_compressed_zero,
  bls12_381_G1_compressed_generator,
  BuiltinBLS12_381_G2_Element,
  bls12_381_G2_equals,
  bls12_381_G2_add,
  bls12_381_G2_neg,
  bls12_381_G2_scalarMul,
  bls12_381_G2_compress,
  bls12_381_G2_uncompress,
  bls12_381_G2_hashToGroup,
  bls12_381_G2_compressed_zero,
  bls12_381_G2_compressed_generator,
  BuiltinBLS12_381_MlResult,
  bls12_381_millerLoop,
  bls12_381_mulMlResult,
  bls12_381_finalVerify,

  -- * Conversions
  fromBuiltin,
  toBuiltin,
  fromOpaque,
  toOpaque,
  integerToByteString,
  byteStringToInteger,
) where

import Data.String (IsString (..))
import PlutusCore.Data (Data (..))
import PlutusTx.Applicative as Applicative
import PlutusTx.Base as Base
import PlutusTx.Bool as Bool
import PlutusTx.Builtins (BuiltinBLS12_381_G1_Element, BuiltinBLS12_381_G2_Element,
                          BuiltinBLS12_381_MlResult, BuiltinByteString, BuiltinByteStringUtf8 (..),
                          BuiltinData, BuiltinString, Integer, appendByteString, appendString,
                          blake2b_224, blake2b_256, bls12_381_G1_add, bls12_381_G1_compress,
                          bls12_381_G1_compressed_generator, bls12_381_G1_compressed_zero,
                          bls12_381_G1_equals, bls12_381_G1_hashToGroup, bls12_381_G1_neg,
                          bls12_381_G1_scalarMul, bls12_381_G1_uncompress, bls12_381_G2_add,
                          bls12_381_G2_compress, bls12_381_G2_compressed_generator,
                          bls12_381_G2_compressed_zero, bls12_381_G2_equals,
                          bls12_381_G2_hashToGroup, bls12_381_G2_neg, bls12_381_G2_scalarMul,
                          bls12_381_G2_uncompress, bls12_381_finalVerify, bls12_381_millerLoop,
                          bls12_381_mulMlResult, byteStringToInteger, consByteString, decodeUtf8,
                          emptyByteString, emptyString, encodeUtf8, equalsByteString, equalsString,
                          error, fromBuiltin, fromOpaque, greaterThanByteString, indexByteString,
                          integerToByteString, keccak_256, lengthOfByteString, lessThanByteString,
                          ripemd_160, sha2_256, sha3_256, sliceByteString, toBuiltin, toOpaque,
                          trace, verifyEcdsaSecp256k1Signature, verifyEd25519Signature,
                          verifySchnorrSecp256k1Signature)

import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Either as Either
import PlutusTx.Enum as Enum
import PlutusTx.Eq as Eq
import PlutusTx.ErrorCodes
import PlutusTx.Foldable as Foldable
import PlutusTx.Function as Function
import PlutusTx.Functor as Functor
import PlutusTx.IsData
import PlutusTx.Lattice as Lattice
import PlutusTx.List as List hiding (concat, concatMap, foldl, foldr)
import PlutusTx.Maybe as Maybe
import PlutusTx.Monoid as Monoid
import PlutusTx.Numeric as Numeric
import PlutusTx.Ord as Ord
import PlutusTx.Ratio as Ratio
import PlutusTx.Semigroup as Semigroup
import PlutusTx.Trace as Trace
import PlutusTx.Traversable as Traversable

import Prelude qualified as Haskell (return, (=<<), (>>), (>>=))

-- | Checks a 'Bool' and aborts if it is false.
check :: Bool -> BI.BuiltinUnit
check b = if b then BI.unitval else traceError checkHasFailedError
{-# INLINEABLE check #-}

{-| Integer division, rounding downwards

  >>> divide (-41) 5
  -9
-}
divide :: Integer -> Integer -> Integer
divide = Builtins.divideInteger
{-# INLINEABLE divide #-}

{-| Integer remainder, always positive for a positive divisor

  >>> modulo (-41) 5
  4
-}
modulo :: Integer -> Integer -> Integer
modulo = Builtins.modInteger
{-# INLINEABLE modulo #-}

-- | FIXME (https://github.com/IntersectMBO/plutus-private/issues/1729)
expMod :: Integer -> Integer -> Integer -> Integer
expMod = Builtins.expModInteger
{-# INLINEABLE expMod #-}

{-| Integer division, rouding towards zero

  >>> quotient (-41) 5
  -8
-}
{-# INLINEABLE quotient #-}
quotient :: Integer -> Integer -> Integer
quotient = Builtins.quotientInteger

{-| Integer remainder, same sign as dividend

  >>> remainder (-41) 5
  -1
-}
remainder :: Integer -> Integer -> Integer
remainder = Builtins.remainderInteger
{-# INLINEABLE remainder #-}

even :: Integer -> Bool
even n = if modulo n 2 == 0 then True else False
{-# INLINEABLE even #-}

odd :: Integer -> Bool
odd n = if even n then False else True
{-# INLINEABLE odd #-}

-- | Returns the n length prefix of a 'ByteString'.
takeByteString :: Integer -> BuiltinByteString -> BuiltinByteString
takeByteString n bs = Builtins.sliceByteString 0 n bs
{-# INLINEABLE takeByteString #-}

-- | Returns the suffix of a 'ByteString' after n elements.
dropByteString :: Integer -> BuiltinByteString -> BuiltinByteString
dropByteString n bs = Builtins.sliceByteString n (Builtins.lengthOfByteString bs - n) bs
{-# INLINEABLE dropByteString #-}

{- Note [-fno-full-laziness in Plutus Tx]
GHC's full-laziness optimization moves computations inside a lambda that don't depend on
the lambda-bound variable out of the lambda, in order to avoid repeating the computations
unnecessarily. For Plutus Tx, this is not only not useful but is harmful.

It is not useful because we do not use lazy evaluation for Plutus Tx, so a non-strict
binding is evaluated exactly the same number of times, whether or not it is inside
a lambda.

It can be harmful because it can turn

```
\unused -> case x_lazy of x_evaluated -> ...x_evaluated...
```

into

```
let y = ...x_lazy...
 in \unused -> case x_lazy of _ -> y
```

These two expressions are equivalent in Haskell. In Plutus Tx, howver, the first one
evaluates `x_lazy` once, and then uses `x_evaluated` subsequently. The second one,
on the other hand, evaluates `x_lazy` but discards the result, and may evaluate
`x_lazy` again when evaluating `y`! We therefore must turn off full laziness in
Plutus Tx code.
-}
