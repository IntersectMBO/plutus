-- | Primitive names and functions for working with Plutus Core builtins.
module Language.Plutus.CoreToPLC.Builtins where

import           Data.ByteString.Lazy
import           Language.Plutus.CoreToPLC.Error

-- TODO: resizing primitives? better handling of sizes?

concatenate :: ByteString -> ByteString -> ByteString
concatenate = mustBeReplaced

takeByteString :: Int -> ByteString -> ByteString
takeByteString = mustBeReplaced

dropByteString :: Int -> ByteString -> ByteString
dropByteString = mustBeReplaced

sha2_256 :: ByteString -> ByteString
sha2_256 = mustBeReplaced

sha3_256 :: ByteString -> ByteString
sha3_256 = mustBeReplaced

verifySignature :: ByteString -> ByteString -> ByteString -> Bool
verifySignature = mustBeReplaced

equalsByteString :: ByteString -> ByteString -> Bool
equalsByteString = mustBeReplaced

txhash :: ByteString
txhash = mustBeReplaced

blocknum :: Int
blocknum = mustBeReplaced

addInteger :: Int -> Int -> Int
addInteger = mustBeReplaced

subtractInteger :: Int -> Int -> Int
subtractInteger = mustBeReplaced

multiplyInteger :: Int -> Int -> Int
multiplyInteger = mustBeReplaced

divideInteger :: Int -> Int -> Int
divideInteger = mustBeReplaced

remainderInteger :: Int -> Int -> Int
remainderInteger = mustBeReplaced

greaterThanInteger :: Int -> Int -> Bool
greaterThanInteger = mustBeReplaced

greaterThanEqInteger :: Int -> Int -> Bool
greaterThanEqInteger = mustBeReplaced

lessThanInteger :: Int -> Int -> Bool
lessThanInteger = mustBeReplaced

lessThanEqInteger :: Int -> Int -> Bool
lessThanEqInteger = mustBeReplaced

equalsInteger :: Int -> Int -> Bool
equalsInteger = mustBeReplaced

error :: () -> a
error = mustBeReplaced
