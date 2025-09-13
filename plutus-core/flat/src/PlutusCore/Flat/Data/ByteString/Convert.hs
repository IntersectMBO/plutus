{-# LANGUAGE FlexibleInstances #-}

module PlutusCore.Flat.Data.ByteString.Convert
  ( AsByteString(..)
  )
where

import Data.ByteString qualified as B
import Data.ByteString.Lazy qualified as L
import Data.Word

-- |Convert to/from strict ByteStrings
class AsByteString a where
  toByteString :: a -> B.ByteString
  fromByteString :: B.ByteString -> a

instance AsByteString B.ByteString where
  toByteString   = id
  fromByteString = id

instance AsByteString L.ByteString where
  toByteString   = L.toStrict
  fromByteString = L.fromStrict

instance AsByteString [Word8] where
  toByteString   = B.pack
  fromByteString = B.unpack

