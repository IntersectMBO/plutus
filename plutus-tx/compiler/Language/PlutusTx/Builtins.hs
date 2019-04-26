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

takeByteString :: Int -> ByteString -> ByteString
takeByteString i = BSL.take (fromIntegral i)

dropByteString :: Int -> ByteString -> ByteString
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

addInteger :: Int -> Int -> Int
addInteger = (+)

subtractInteger :: Int -> Int -> Int
subtractInteger = (-)

multiplyInteger :: Int -> Int -> Int
multiplyInteger = (*)

divideInteger :: Int -> Int -> Int
divideInteger = div

remainderInteger :: Int -> Int -> Int
remainderInteger = rem

greaterThanInteger :: Int -> Int -> Bool
greaterThanInteger = (>)

greaterThanEqInteger :: Int -> Int -> Bool
greaterThanEqInteger = (>=)

lessThanInteger :: Int -> Int -> Bool
lessThanInteger = (<)

lessThanEqInteger :: Int -> Int -> Bool
lessThanEqInteger = (<=)

equalsInteger :: Int -> Int -> Bool
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
