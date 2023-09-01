-- editorconfig-checker-disable-file
-- Need some extra imports from the Prelude for doctests, annoyingly
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fmax-simplifier-iterations=0 #-}

module PlutusTx.Prelude (
    -- $prelude
    -- * Classes
    module Eq,
    module Enum,
    module Ord,
    module Semigroup,
    module Monoid,
    module Numeric,
    module Functor,
    module Applicative,
    module Lattice,
    module Foldable,
    module Traversable,
    -- * Monad
    (Haskell.>>=),
    (Haskell.=<<),
    (Haskell.>>),
    Haskell.return,
    -- * Standard functions, Tuples
    module Base,
    -- * Tracing functions
    module Trace,
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
    -- * Maybe
    module Maybe,
    -- * Either
    module Either,
    -- * Lists
    module List,
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
    -- * Hashes and Signatures
    sha2_256,
    sha3_256,
    blake2b_224,
    blake2b_256,
    keccak_256,
    verifyEd25519Signature,
    verifyEcdsaSecp256k1Signature,
    verifySchnorrSecp256k1Signature,
    -- * Rational numbers
    Rational,
    unsafeRatio,
    ratio,
    fromInteger,
    round,
    -- * Data
    BuiltinData,
    -- * BLS12_381
    BuiltinBLS12_381_G1_Element,
    bls12_381_G1_equals,
    bls12_381_G1_add,
    bls12_381_G1_neg,
    bls12_381_G1_scalarMul,
    bls12_381_G1_compress,
    bls12_381_G1_uncompress,
    bls12_381_G1_hashToGroup,
    bls12_381_G1_zero,
    bls12_381_G1_generator,
    BuiltinBLS12_381_G2_Element,
    bls12_381_G2_equals,
    bls12_381_G2_add,
    bls12_381_G2_neg,
    bls12_381_G2_scalarMul,
    bls12_381_G2_compress,
    bls12_381_G2_uncompress,
    bls12_381_G2_hashToGroup,
    bls12_381_G2_zero,
    bls12_381_G2_generator,
    BuiltinBLS12_381_MlResult,
    bls12_381_millerLoop,
    bls12_381_mulMlResult,
    bls12_381_finalVerify,
    -- * Conversions
    fromBuiltin,
    toBuiltin
    ) where

import Data.String (IsString (..))
import PlutusCore.Data (Data (..))
import PlutusTx.Applicative as Applicative
import PlutusTx.Base as Base
import PlutusTx.Bool as Bool
import PlutusTx.Builtins (BuiltinBLS12_381_G1_Element, BuiltinBLS12_381_G2_Element,
                          BuiltinBLS12_381_MlResult, BuiltinByteString, BuiltinData, BuiltinString,
                          Integer, appendByteString, appendString, blake2b_224, blake2b_256,
                          bls12_381_G1_add, bls12_381_G1_compress, bls12_381_G1_equals,
                          bls12_381_G1_generator, bls12_381_G1_hashToGroup, bls12_381_G1_neg,
                          bls12_381_G1_scalarMul, bls12_381_G1_uncompress, bls12_381_G1_zero,
                          bls12_381_G2_add, bls12_381_G2_compress, bls12_381_G2_equals,
                          bls12_381_G2_generator, bls12_381_G2_hashToGroup, bls12_381_G2_neg,
                          bls12_381_G2_scalarMul, bls12_381_G2_uncompress, bls12_381_G2_zero,
                          bls12_381_finalVerify, bls12_381_millerLoop, bls12_381_mulMlResult,
                          consByteString, decodeUtf8, emptyByteString, emptyString, encodeUtf8,
                          equalsByteString, equalsString, error, fromBuiltin, greaterThanByteString,
                          indexByteString, keccak_256, lengthOfByteString, lessThanByteString,
                          sha2_256, sha3_256, sliceByteString, toBuiltin, trace,
                          verifyEcdsaSecp256k1Signature, verifyEd25519Signature,
                          verifySchnorrSecp256k1Signature)

import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Either as Either
import PlutusTx.Enum as Enum
import PlutusTx.Eq as Eq
import PlutusTx.ErrorCodes
import PlutusTx.Foldable as Foldable
import PlutusTx.Functor as Functor
import PlutusTx.IsData
import PlutusTx.Lattice as Lattice
import PlutusTx.List as List hiding (foldr)
import PlutusTx.Maybe as Maybe
import PlutusTx.Monoid as Monoid
import PlutusTx.Numeric as Numeric
import PlutusTx.Ord as Ord
import PlutusTx.Ratio as Ratio
import PlutusTx.Semigroup as Semigroup
import PlutusTx.Trace as Trace
import PlutusTx.Traversable as Traversable

import Prelude qualified as Haskell (return, (=<<), (>>), (>>=))

-- this module does lots of weird stuff deliberately
{- HLINT ignore -}

-- $prelude
-- The PlutusTx Prelude is a replacement for the Haskell Prelude that works
-- better with Plutus Tx. You should use it if you're writing code that
-- will be compiled with the Plutus Tx compiler.
-- @
--     {-# LANGUAGE NoImplicitPrelude #-}
--     import PlutusTx.Prelude
-- @

-- $setup
-- >>> :set -XNoImplicitPrelude
-- >>> import PlutusTx.Prelude

{-# INLINABLE check #-}
-- | Checks a 'Bool' and aborts if it is false.
check :: Bool -> ()
check b = if b then () else traceError checkHasFailedError

{-# INLINABLE divide #-}
-- | Integer division, rounding downwards
--
--   >>> divide (-41) 5
--   -9
--
divide :: Integer -> Integer -> Integer
divide = Builtins.divideInteger

{-# INLINABLE modulo #-}
-- | Integer remainder, always positive for a positive divisor
--
--   >>> modulo (-41) 5
--   4
--
modulo :: Integer -> Integer -> Integer
modulo = Builtins.modInteger

{-# INLINABLE quotient #-}
-- | Integer division, rouding towards zero
--
--   >>> quotient (-41) 5
--   -8
--

quotient :: Integer -> Integer -> Integer
quotient = Builtins.quotientInteger

{-# INLINABLE remainder #-}
-- | Integer remainder, same sign as dividend
--
--   >>> remainder (-41) 5
--   -1
--
remainder :: Integer -> Integer -> Integer
remainder = Builtins.remainderInteger

{-# INLINABLE even #-}
even :: Integer -> Bool
even n = if modulo n 2 == 0 then True else False

{-# INLINABLE odd #-}
odd :: Integer -> Bool
odd n = if even n then False else True

{-# INLINABLE takeByteString #-}
-- | Returns the n length prefix of a 'ByteString'.
takeByteString :: Integer -> BuiltinByteString -> BuiltinByteString
takeByteString n bs = Builtins.sliceByteString 0 (toBuiltin n) bs

{-# INLINABLE dropByteString #-}
-- | Returns the suffix of a 'ByteString' after n elements.
dropByteString :: Integer -> BuiltinByteString -> BuiltinByteString
dropByteString n bs = Builtins.sliceByteString (toBuiltin n) (Builtins.lengthOfByteString bs - n) bs

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
