{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
-- | Primitive names and functions for working with Plutus Core builtins.
module Language.PlutusTx.Builtins (
                                -- * Bytestring builtins
                                ByteString
                                , concatenate
                                , takeByteString
                                , dropByteString
                                , emptyByteString
                                , equalsByteString
                                , sha2_256
                                , sha3_256
                                , verifySignature
                                -- * Integer builtins
                                , addInteger
                                , subtractInteger
                                , multiplyInteger
                                , divideInteger
                                , remainderInteger
                                , greaterThanInteger
                                , greaterThanEqInteger
                                , lessThanInteger
                                , lessThanEqInteger
                                , equalsInteger
                                -- * Error
                                , error
                                -- * Strings
                                , String
                                , appendString
                                , emptyString
                                , charToString
                                -- * Tracing
                                , trace
                                ) where

import qualified Crypto
import           Data.ByteString.Lazy      as BSL
import qualified Data.ByteString.Lazy.Hash as Hash
import           Data.Maybe                (fromMaybe)
import           Prelude                   hiding (String, error)

import           Language.PlutusTx.Utils   (mustBeReplaced)

{- Note [Builtin name definitions]
The builtins here have definitions so they can be used in off-chain code too.

However they *must* be replaced by the compiler when used in Plutus Tx code, so
in particular they must *not* be inlined, otherwise we can't spot them to replace
them.
-}

{-# NOINLINE concatenate #-}
concatenate :: ByteString -> ByteString -> ByteString
concatenate = BSL.append

{-# NOINLINE takeByteString #-}
takeByteString :: Integer -> ByteString -> ByteString
takeByteString i = BSL.take (fromIntegral i)

{-# NOINLINE dropByteString #-}
dropByteString :: Integer -> ByteString -> ByteString
dropByteString i = BSL.drop (fromIntegral i)

{-# NOINLINE emptyByteString #-}
emptyByteString :: ByteString
emptyByteString = BSL.empty

{-# NOINLINE sha2_256 #-}
sha2_256 :: ByteString -> ByteString
sha2_256 = Hash.sha2

{-# NOINLINE sha3_256 #-}
sha3_256 :: ByteString -> ByteString
sha3_256 = Hash.sha3

{-# NOINLINE verifySignature #-}
verifySignature :: ByteString -> ByteString -> ByteString -> Bool
verifySignature pubKey message signature =
  fromMaybe False (Crypto.verifySignature pubKey message signature)

{-# NOINLINE equalsByteString #-}
equalsByteString :: ByteString -> ByteString -> Bool
equalsByteString = (==)

{-# NOINLINE addInteger #-}
addInteger :: Integer -> Integer -> Integer
addInteger = (+)

{-# NOINLINE subtractInteger #-}
subtractInteger :: Integer -> Integer -> Integer
subtractInteger = (-)

{-# NOINLINE multiplyInteger #-}
multiplyInteger :: Integer -> Integer -> Integer
multiplyInteger = (*)

{-# NOINLINE divideInteger #-}
divideInteger :: Integer -> Integer -> Integer
divideInteger = div

{-# NOINLINE remainderInteger #-}
remainderInteger :: Integer -> Integer -> Integer
remainderInteger = rem

{-# NOINLINE greaterThanInteger #-}
greaterThanInteger :: Integer -> Integer -> Bool
greaterThanInteger = (>)

{-# NOINLINE greaterThanEqInteger #-}
greaterThanEqInteger :: Integer -> Integer -> Bool
greaterThanEqInteger = (>=)

{-# NOINLINE lessThanInteger #-}
lessThanInteger :: Integer -> Integer -> Bool
lessThanInteger = (<)

{-# NOINLINE lessThanEqInteger #-}
lessThanEqInteger :: Integer -> Integer -> Bool
lessThanEqInteger = (<=)

{-# NOINLINE equalsInteger #-}
equalsInteger :: Integer -> Integer -> Bool
equalsInteger = (==)

{-# NOINLINE error #-}
error :: () -> a
error = mustBeReplaced "error"

-- | An opaque type representing PLC strings.
data String

{-# NOINLINE appendString #-}
appendString :: String -> String -> String
appendString = mustBeReplaced "appendString"

{-# NOINLINE emptyString #-}
emptyString :: String
emptyString = mustBeReplaced "emptyString"

{-# NOINLINE charToString #-}
charToString :: Char -> String
charToString = mustBeReplaced "charToString"

{-# NOINLINE trace #-}
trace :: String -> ()
trace = mustBeReplaced "trace"
