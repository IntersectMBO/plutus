{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
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

concatenate :: ByteString -> ByteString -> ByteString
concatenate = BSL.append

takeByteString :: Integer -> ByteString -> ByteString
takeByteString i = BSL.take (fromIntegral i)

dropByteString :: Integer -> ByteString -> ByteString
dropByteString i = BSL.drop (fromIntegral i)

emptyByteString :: ByteString
emptyByteString = BSL.empty

sha2_256 :: ByteString -> ByteString
sha2_256 = Hash.sha2

sha3_256 :: ByteString -> ByteString
sha3_256 = Hash.sha3

verifySignature :: ByteString -> ByteString -> ByteString -> Bool
verifySignature pubKey message signature =
  fromMaybe False (Crypto.verifySignature pubKey message signature)

equalsByteString :: ByteString -> ByteString -> Bool
equalsByteString = (==)

addInteger :: Integer -> Integer -> Integer
addInteger = (+)

subtractInteger :: Integer -> Integer -> Integer
subtractInteger = (-)

multiplyInteger :: Integer -> Integer -> Integer
multiplyInteger = (*)

divideInteger :: Integer -> Integer -> Integer
divideInteger = div

remainderInteger :: Integer -> Integer -> Integer
remainderInteger = rem

greaterThanInteger :: Integer -> Integer -> Bool
greaterThanInteger = (>)

greaterThanEqInteger :: Integer -> Integer -> Bool
greaterThanEqInteger = (>=)

lessThanInteger :: Integer -> Integer -> Bool
lessThanInteger = (<)

lessThanEqInteger :: Integer -> Integer -> Bool
lessThanEqInteger = (<=)

equalsInteger :: Integer -> Integer -> Bool
equalsInteger = (==)

error :: () -> a
error = mustBeReplaced

-- | An opaque type representing PLC strings.
data String

appendString :: String -> String -> String
appendString = mustBeReplaced

emptyString :: String
emptyString = mustBeReplaced

charToString :: Char -> String
charToString = mustBeReplaced

trace :: String -> ()
trace = mustBeReplaced
