-- |
-- Module      : Foundation.Network.IPv4
-- License     : BSD-style
-- Maintainer  : Nicolas Di Prima <nicolas@primetype.co.uk>
-- Stability   : experimental
-- Portability : portable
--
-- IPv4 data type
--
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Foundation.Network.IPv4
    ( IPv4
    , any, loopback
    , fromString, toString
    , fromTuple, toTuple
    , ipv4Parser
    ) where

import Prelude (fromIntegral)

import Foundation.Class.Storable
import Foundation.Hashing.Hashable
import Basement.Compat.Base
import Data.Proxy
import Foundation.String (String)
import Foundation.Primitive
import Basement.Bits
import Foundation.Parser hiding (peek)
import Foundation.Collection (Sequential, Element, elem)
import Text.Read (readMaybe)

-- | IPv4 data type
newtype IPv4 = IPv4 Word32
    deriving (Eq, Ord, Typeable, Hashable)
instance Show IPv4 where
    show = toLString
instance NormalForm IPv4 where
    toNormalForm !_ = ()
instance IsString IPv4 where
    fromString = fromLString
instance Storable IPv4 where
    peek ptr = IPv4 . fromBE <$> peek (castPtr ptr)
    poke ptr (IPv4 w) = poke (castPtr ptr) (toBE w)
instance StorableFixed IPv4 where
    size      _ = size      (Proxy :: Proxy Word32)
    alignment _ = alignment (Proxy :: Proxy Word32)

-- | "0.0.0.0"
any :: IPv4
any = fromTuple (0,0,0,0)

-- | "127.0.0.1"
loopback :: IPv4
loopback = fromTuple (127,0,0,1)

toString :: IPv4 -> String
toString = fromList . toLString

fromLString :: [Char] -> IPv4
fromLString = either throw id . parseOnly ipv4Parser

toLString :: IPv4 -> [Char]
toLString ipv4 =
    let (i1, i2, i3, i4) = toTuple ipv4
     in show i1 <> "." <> show i2 <> "." <> show i3 <> "." <> show i4

fromTuple :: (Word8, Word8, Word8, Word8) -> IPv4
fromTuple (i1, i2, i3, i4) =
     IPv4 $     (w1 .<<. 24) .&. 0xFF000000
            .|. (w2 .<<. 16) .&. 0x00FF0000
            .|. (w3 .<<.  8) .&. 0x0000FF00
            .|.  w4          .&. 0x000000FF
  where
    f = fromIntegral
    w1, w2, w3, w4 :: Word32
    w1 = f i1
    w2 = f i2
    w3 = f i3
    w4 = f i4

toTuple :: IPv4 -> (Word8, Word8, Word8, Word8)
toTuple (IPv4 w) =
    (f w1, f w2, f w3, f w4)
  where
    f = fromIntegral
    w1, w2, w3, w4 :: Word32
    w1 = w .>>. 24 .&. 0x000000FF
    w2 = w .>>. 16 .&. 0x000000FF
    w3 = w .>>.  8 .&. 0x000000FF
    w4 = w         .&. 0x000000FF

-- | Parse a IPv4 address
ipv4Parser :: ( ParserSource input, Element input ~ Char
              , Sequential (Chunk input), Element input ~ Element (Chunk input)
              )
           => Parser input IPv4
ipv4Parser = do
    i1 <- takeAWord8 <* element '.'
    i2 <- takeAWord8 <* element '.'
    i3 <- takeAWord8 <* element '.'
    i4 <- takeAWord8
    return $ fromTuple (i1, i2, i3, i4)
  where
    takeAWord8 = do
      maybeN <- readMaybe @Integer . toList <$> takeWhile isAsciiDecimal
      case maybeN of
        Nothing -> reportError $ Satisfy $ Just "expected integer"
        Just n | n > 256   -> reportError $ Satisfy $ Just "expected smaller integer than 256"
               | otherwise -> pure (fromIntegral n)

    isAsciiDecimal = flip elem ['0'..'9']
