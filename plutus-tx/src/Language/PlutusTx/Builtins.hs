{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
-- This ensures that we don't put *anything* about these functions into the interface
-- file, otherwise GHC can be clever about the ones that are always error, even though
-- they're NOINLINE!
{-# OPTIONS_GHC -O0 #-}
-- | Primitive names and functions for working with Plutus Core builtins.
module Language.PlutusTx.Builtins (
                                -- * Bytestring builtins
                                ByteString
                                , concatenate
                                , takeByteString
                                , dropByteString
                                , emptyByteString
                                , equalsByteString
                                , lessThanByteString
                                , greaterThanByteString
                                , sha2_256
                                , sha3_256
                                , verifySignature
                                -- * Integer builtins
                                , addInteger
                                , subtractInteger
                                , multiplyInteger
                                , divideInteger
                                , modInteger
                                , quotientInteger
                                , remainderInteger
                                , greaterThanInteger
                                , greaterThanEqInteger
                                , lessThanInteger
                                , lessThanEqInteger
                                , equalsInteger
                                -- * Error
                                , error
                                -- * Data
                                , Data (..)
                                -- * Strings
                                , String
                                , appendString
                                , emptyString
                                , charToString
                                -- * Tracing
                                , trace
                                ) where

import qualified Crypto
import           Data.ByteString         as BS
import qualified Data.ByteString.Hash    as Hash
import           Data.Maybe              (fromMaybe)
import           Prelude                 hiding (String, error)

import           Language.PlutusTx.Data
import           Language.PlutusTx.Utils (mustBeReplaced)

{- Note [Builtin name definitions]
The builtins here have definitions so they can be used in off-chain code too.

However they *must* be replaced by the compiler when used in Plutus Tx code, so
in particular they must *not* be inlined, otherwise we can't spot them to replace
them.
-}

{-# NOINLINE concatenate #-}
-- | Concatenates two 'ByteString's.
concatenate :: ByteString -> ByteString -> ByteString
concatenate = BS.append

{-# NOINLINE takeByteString #-}
-- | Returns the n length prefix of a 'ByteString'.
takeByteString :: Integer -> ByteString -> ByteString
takeByteString n = BS.take (fromIntegral n)

{-# NOINLINE dropByteString #-}
-- | Returns the suffix of a 'ByteString' after n elements.
dropByteString :: Integer -> ByteString -> ByteString
dropByteString n = BS.drop (fromIntegral n)

{-# NOINLINE emptyByteString #-}
-- | An empty 'ByteString'.
emptyByteString :: ByteString
emptyByteString = BS.empty

{-# NOINLINE sha2_256 #-}
-- | The SHA2-256 hash of a 'ByteString'
sha2_256 :: ByteString -> ByteString
sha2_256 = Hash.sha2

{-# NOINLINE sha3_256 #-}
-- | The SHA3-256 hash of a 'ByteString'
sha3_256 :: ByteString -> ByteString
sha3_256 = Hash.sha3

{-# NOINLINE verifySignature #-}
-- | Verify that the signature is a signature of the message by the public key.
verifySignature :: ByteString -> ByteString -> ByteString -> Bool
verifySignature pubKey message signature =
  fromMaybe False (Crypto.verifySignature pubKey message signature)

{-# NOINLINE equalsByteString #-}
-- | Check if two 'ByteString's are equal.
equalsByteString :: ByteString -> ByteString -> Bool
equalsByteString = (==)

{-# NOINLINE lessThanByteString #-}
-- | Check if one 'ByteString' is less than another.
lessThanByteString :: ByteString -> ByteString -> Bool
lessThanByteString = (<)

{-# NOINLINE greaterThanByteString #-}
-- | Check if one 'ByteString' is greater than another.
greaterThanByteString :: ByteString -> ByteString -> Bool
greaterThanByteString = (>)

{-# NOINLINE addInteger #-}
-- | Add two 'Integer's.
addInteger :: Integer -> Integer -> Integer
addInteger = (+)

{-# NOINLINE subtractInteger #-}
-- | Subtract two 'Integer's.
subtractInteger :: Integer -> Integer -> Integer
subtractInteger = (-)

{-# NOINLINE multiplyInteger #-}
-- | Multiply two 'Integer's.
multiplyInteger :: Integer -> Integer -> Integer
multiplyInteger = (*)

{-# NOINLINE divideInteger #-}
-- | Divide two integers.
divideInteger :: Integer -> Integer -> Integer
divideInteger = div

{-# NOINLINE modInteger #-}
-- | Integer modulo operation.
modInteger :: Integer -> Integer -> Integer
modInteger = mod

{-# NOINLINE quotientInteger #-}
-- | Quotient of two integers.
quotientInteger :: Integer -> Integer -> Integer
quotientInteger = quot

{-# NOINLINE remainderInteger #-}
-- | Take the remainder of dividing two 'Integer's.
remainderInteger :: Integer -> Integer -> Integer
remainderInteger = rem

{-# NOINLINE greaterThanInteger #-}
-- | Check whether one 'Integer' is greater than another.
greaterThanInteger :: Integer -> Integer -> Bool
greaterThanInteger = (>)

{-# NOINLINE greaterThanEqInteger #-}
-- | Check whether one 'Integer' is greater than or equal to another.
greaterThanEqInteger :: Integer -> Integer -> Bool
greaterThanEqInteger = (>=)

{-# NOINLINE lessThanInteger #-}
-- | Check whether one 'Integer' is less than another.
lessThanInteger :: Integer -> Integer -> Bool
lessThanInteger = (<)

{-# NOINLINE lessThanEqInteger #-}
-- | Check whether one 'Integer' is less than or equal to another.
lessThanEqInteger :: Integer -> Integer -> Bool
lessThanEqInteger = (<=)

{-# NOINLINE equalsInteger #-}
-- | Check if two 'Integer's are equal.
equalsInteger :: Integer -> Integer -> Bool
equalsInteger = (==)

{- Note [Delaying error]
The Plutus Core 'error' builtin is of type 'forall a . a', but the
one we expose here is of type 'forall a . () -> a'.

This is because it's hard to get the evaluation order right with
the non-delayed version - it's easy to end up with it getting thrown
unconditionally, or before some other effect (e.g. tracing). On the other
hand, it's much easier to work with the delayed version.

But why not just define that in the library? i.e.

    error = \_ -> Builtins.error

The answer is that GHC is eager to inline and reduce this function, which
does the Wrong Thing. We can't stop GHC doing this (at the moment), but
for most of our functions it's not a *semantic* problem. Here, however,
it is a problem. So we just expose the delayed version as the builtin.
-}

{-# NOINLINE error #-}
-- | Aborts evaluation with an error.
error :: () -> a
error = mustBeReplaced "error"

-- Note: IsString instance is in 'Prelude.hs'
-- | An opaque type representing Plutus Core strings.
data String

{-# NOINLINE appendString #-}
-- | Append two 'String's.
appendString :: String -> String -> String
appendString = mustBeReplaced "appendString"

{-# NOINLINE emptyString #-}
-- | An empty 'String'.
emptyString :: String
emptyString = mustBeReplaced "emptyString"

{-# NOINLINE charToString #-}
-- | Turn a 'Char' into a 'String'.
charToString :: Char -> String
charToString = mustBeReplaced "charToString"

{-# NOINLINE trace #-}
-- | Logs the given 'String' to the evaluation log.
trace :: String -> ()
trace _ = () --mustBeReplaced "trace"
