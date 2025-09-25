{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |Pre-value and post-value byte alignments
module PlutusCore.Flat.Filler (
    Filler(..),
    fillerLength,
    PreAligned(..),
    preAligned,
    PostAligned(..),
    postAligned,
    preAlignedDecoder,
    postAlignedDecoder
    ) where

import Control.DeepSeq (NFData)
import Data.Typeable (Typeable)
import PlutusCore.Flat.Class (Flat (..), Generic)
import PlutusCore.Flat.Decoder.Types (Get)
import PlutusCore.Flat.Encoder.Strict (eFiller, sFillerMax)

-- |A meaningless sequence of 0 bits terminated with a 1 bit (easier to implement than the reverse)
--
-- Used to align encoded values at byte/word boundaries.
data Filler = FillerBit !Filler
            | FillerEnd
  deriving (Show, Eq, Ord, Generic, NFData)

-- |Use a special encoding for the filler
instance Flat Filler where
  encode _ = eFiller
  size = sFillerMax
  -- use generated decode

-- |A Post aligned value, a value followed by a filler
--
-- Useful to complete the encoding of a top-level value
#ifdef ETA_VERSION

data PostAligned a = PostAligned { postValue :: a, postFiller :: Filler }
  deriving (Show, Eq, Ord, Generic, NFData)

instance Flat a => Flat (PostAligned a) where
  encode (PostAligned val fill) = trampolineEncoding (encode val) <> encode fill

#else

data PostAligned a = PostAligned { postValue :: a, postFiller :: Filler }
  deriving (Show, Eq, Ord, Generic, NFData,Flat)

#endif

-- |A Pre aligned value, a value preceded by a filler
--
-- Useful to prealign ByteArrays, Texts and any structure that can be encoded more efficiently when byte aligned.
data PreAligned a = PreAligned { preFiller :: Filler, preValue :: a }
  deriving (Show, Eq, Ord, Generic, NFData, Flat)

-- |Length of a filler in bits
fillerLength :: Num a => Filler -> a
fillerLength FillerEnd     = 1
fillerLength (FillerBit f) = 1 + fillerLength f

-- |Post align a value
postAligned :: a -> PostAligned a
postAligned a = PostAligned a FillerEnd

-- |Pre align a value
preAligned :: a -> PreAligned a
preAligned = PreAligned FillerEnd

-- |Decode a value assuming that is PostAligned
postAlignedDecoder :: Get b -> Get b
postAlignedDecoder dec = do
  v <- dec
  _::Filler <- decode
  return v

-- |Decode a value assuming that is PreAligned
--
-- @since 0.5
preAlignedDecoder :: Get b -> Get b
preAlignedDecoder dec = do
  _::Filler <- decode
  dec
