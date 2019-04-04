{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# OPTIONS_GHC -O0 #-}
-- | Primitive names and functions for working with Plutus Core builtins.
module Language.PlutusTx.Builtins (
                                -- * Bytestring builtins
                                SizedByteString(..)
                                , ByteString
                                , resizeByteString
                                , concatenate
                                , takeByteString
                                , dropByteString
                                , sha2_256
                                , sha3_256
                                , verifySignature
                                , equalsByteString
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

import           Codec.Serialise
import qualified Crypto
import qualified Data.ByteString.Lazy      as BSL
import qualified Data.ByteString.Lazy.Hash as Hash
import           Data.Maybe                (fromMaybe)
import           Data.String               (IsString)
import           GHC.TypeLits
import           Prelude                   hiding (String, error)

import           Language.PlutusTx.Utils   (mustBeReplaced)

-- TODO: resizing primitives? better handling of sizes?

-- | A sized bytestring.
newtype SizedByteString (s::Nat) = SizedByteString { unSizedByteString :: BSL.ByteString }
        deriving (Eq, Ord, Show, IsString, Serialise)

-- | A bytestring of default size (32 bytes).
type ByteString = SizedByteString 32

resizeByteString :: SizedByteString s1 -> SizedByteString s2
resizeByteString (SizedByteString b) = SizedByteString b

concatenate :: SizedByteString s -> SizedByteString s -> SizedByteString s
concatenate (SizedByteString l) (SizedByteString r) = SizedByteString (BSL.append l r)

takeByteString :: Int -> SizedByteString s -> SizedByteString s
takeByteString i (SizedByteString bs) = SizedByteString (BSL.take (fromIntegral i) bs)

dropByteString :: Int -> SizedByteString s -> SizedByteString s
dropByteString i (SizedByteString bs) = SizedByteString (BSL.drop (fromIntegral i) bs)

sha2_256 :: SizedByteString s -> SizedByteString 32
sha2_256 (SizedByteString bs) = SizedByteString (Hash.sha2 bs)

sha3_256 :: SizedByteString s -> SizedByteString 32
sha3_256 (SizedByteString bs) = SizedByteString (Hash.sha3 bs)

verifySignature :: SizedByteString 32 -> SizedByteString 32 -> SizedByteString 64 -> Bool
verifySignature (SizedByteString pubKey) (SizedByteString message) (SizedByteString signature) =
  fromMaybe False (Crypto.verifySignature pubKey message signature)

equalsByteString :: SizedByteString s -> SizedByteString s -> Bool
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
