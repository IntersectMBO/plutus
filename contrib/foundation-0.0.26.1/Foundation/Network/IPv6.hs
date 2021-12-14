-- |
-- Module      : Foundation.Network.IPv6
-- License     : BSD-style
-- Maintainer  : Nicolas Di Prima <nicolas@primetype.co.uk>
-- Stability   : experimental
-- Portability : portable
--
-- IPv6 data type
--
{-# LANGUAGE FlexibleInstances #-}

module Foundation.Network.IPv6
    ( IPv6
    , any, loopback
    , fromString, toString
    , fromTuple, toTuple
      -- * parsers
    , ipv6Parser
    , ipv6ParserPreferred
    , ipv6ParserCompressed
    , ipv6ParserIpv4Embedded
    ) where

import Prelude (fromIntegral, read)
import qualified Text.Printf as Base
import Data.Char (isHexDigit, isDigit)
import Numeric (readHex)

import Foundation.Class.Storable
import Foundation.Hashing.Hashable
import Basement.Numerical.Additive (scale)
import Basement.Compat.Base
import Data.Proxy
import Foundation.Primitive
import Basement.Types.OffsetSize
import Foundation.Numerical
import Foundation.Collection (Element, length, intercalate, replicate, null)
import Foundation.Parser
import Foundation.String (String)
import Foundation.Bits

-- | IPv6 data type
data IPv6 = IPv6 {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64
    deriving (Eq, Ord, Typeable)
instance NormalForm IPv6 where
    toNormalForm !_ = ()
instance Hashable IPv6 where
    hashMix (IPv6 w1 w2) = hashMix w1 . hashMix w2
instance Show IPv6 where
    show = toLString
instance IsString IPv6 where
    fromString = fromLString
instance Storable IPv6 where
    peek ptr = fromTuple <$>
        (   (,,,,,,,)
        <$> (fromBE <$> peekOff ptr' 0)
        <*> (fromBE <$> peekOff ptr' 1)
        <*> (fromBE <$> peekOff ptr' 2)
        <*> (fromBE <$> peekOff ptr' 3)
        <*> (fromBE <$> peekOff ptr' 4)
        <*> (fromBE <$> peekOff ptr' 5)
        <*> (fromBE <$> peekOff ptr' 6)
        <*> (fromBE <$> peekOff ptr' 7)
        )
      where
        ptr' :: Ptr (BE Word16)
        ptr' = castPtr ptr
    poke ptr ipv6 = do
        let (i1,i2,i3,i4,i5,i6,i7,i8) = toTuple ipv6
         in pokeOff ptr' 0 (toBE i1)
         >> pokeOff ptr' 1 (toBE i2)
         >> pokeOff ptr' 2 (toBE i3)
         >> pokeOff ptr' 3 (toBE i4)
         >> pokeOff ptr' 4 (toBE i5)
         >> pokeOff ptr' 5 (toBE i6)
         >> pokeOff ptr' 6 (toBE i7)
         >> pokeOff ptr' 7 (toBE i8)
      where
        ptr' :: Ptr (BE Word16)
        ptr' = castPtr ptr
instance StorableFixed IPv6 where
    size      _ = (size      (Proxy :: Proxy Word64)) `scale` 2
    alignment _ = alignment (Proxy :: Proxy Word64)

-- | equivalent to `::`
any :: IPv6
any = fromTuple (0,0,0,0,0,0,0,0)

-- | equivalent to `::1`
loopback :: IPv6
loopback = fromTuple (0,0,0,0,0,0,0,1)

-- | serialise to human readable IPv6
--
-- >>> toString (fromString "0:0:0:0:0:0:0:1" :: IPv6)
toString :: IPv6 -> String
toString = fromList . toLString

toLString :: IPv6 -> [Char]
toLString ipv4 =
    let (i1,i2,i3,i4,i5,i6,i7,i8) = toTuple ipv4
     in intercalate ":" $ showHex4 <$> [i1,i2,i3,i4,i5,i6,i7,i8]

showHex4 :: Word16 -> [Char]
showHex4 = showHex

showHex :: Word16 -> [Char]
showHex = Base.printf "%04x"

fromLString :: [Char] -> IPv6
fromLString = either throw id . parseOnly ipv6Parser


-- | create an IPv6 from the given tuple
fromTuple :: (Word16, Word16, Word16, Word16, Word16, Word16, Word16, Word16)
          -> IPv6
fromTuple (i1, i2, i3, i4, i5, i6, i7, i8) = IPv6 hi low
  where
    f :: Word16 -> Word64
    f = fromIntegral
    hi, low :: Word64
    hi =    (f i1 .<<. 48)
        .|. (f i2 .<<. 32)
        .|. (f i3 .<<. 16)
        .|. (f i4        )
    low =   (f i5 .<<. 48)
        .|. (f i6 .<<. 32)
        .|. (f i7 .<<. 16)
        .|. (f i8        )

-- | decompose an IPv6 into a tuple
toTuple :: IPv6 -> (Word16,Word16,Word16,Word16,Word16,Word16,Word16,Word16)
toTuple (IPv6 hi low) =
    (f w1, f w2, f w3, f w4, f w5, f w6, f w7, f w8)
  where
    f :: Word64 -> Word16
    f = fromIntegral
    w1, w2, w3, w4, w5, w6, w7, w8 :: Word64
    w1 = hi  .>>. 48
    w2 = hi  .>>. 32
    w3 = hi  .>>. 16
    w4 = hi
    w5 = low .>>. 48
    w6 = low .>>. 32
    w7 = low .>>. 16
    w8 = low

-- | IPv6 Parser as described in RFC4291
--
-- for more details: https://tools.ietf.org/html/rfc4291.html#section-2.2
--
-- which is exactly:
--
-- ```
--     ipv6ParserPreferred
-- <|> ipv6ParserIPv4Embedded
-- <|> ipv6ParserCompressed
-- ```
--
ipv6Parser :: (ParserSource input, Element input ~ Char, Element (Chunk input) ~ Char)
           => Parser input IPv6
ipv6Parser =  ipv6ParserPreferred
          <|> ipv6ParserIpv4Embedded
          <|> ipv6ParserCompressed

-- | IPv6 parser as described in RFC4291 section 2.2.1
--
-- The preferred form is x:x:x:x:x:x:x:x, where the 'x's are one to
-- four hexadecimal digits of the eight 16-bit pieces of the address.
--
-- * `ABCD:EF01:2345:6789:ABCD:EF01:2345:6789`
-- * `2001:DB8:0:0:8:800:200C:417A`
--
ipv6ParserPreferred :: (ParserSource input, Element input ~ Char, Element (Chunk input) ~ Char)
                    => Parser input IPv6
ipv6ParserPreferred = do
    i1 <- takeAWord16 <* skipColon
    i2 <- takeAWord16 <* skipColon
    i3 <- takeAWord16 <* skipColon
    i4 <- takeAWord16 <* skipColon
    i5 <- takeAWord16 <* skipColon
    i6 <- takeAWord16 <* skipColon
    i7 <- takeAWord16 <* skipColon
    i8 <- takeAWord16
    return $ fromTuple (i1,i2,i3,i4,i5,i6,i7,i8)


-- | IPv6 address with embedded IPv4 address
--
-- when dealing with a mixed environment of IPv4 and IPv6 nodes is
-- x:x:x:x:x:x:d.d.d.d, where the 'x's are the hexadecimal values of
-- the six high-order 16-bit pieces of the address, and the 'd's are
-- the decimal values of the four low-order 8-bit pieces of the
-- address (standard IPv4 representation).
--
-- * `0:0:0:0:0:0:13.1.68.3`
-- * `0:0:0:0:0:FFFF:129.144.52.38`
-- * `::13.1.68.3`
-- * `::FFFF:129.144.52.38`
--
ipv6ParserIpv4Embedded :: (ParserSource input, Element input ~ Char, Element (Chunk input) ~ Char)
                       => Parser input IPv6
ipv6ParserIpv4Embedded = do
    bs1 <- repeat (Between $ 0 `And` 6 ) $ takeAWord16 <* skipColon
    _ <- optional skipColon
    _ <- optional skipColon
    let (CountOf lenBs1) = length bs1
    bs2 <- repeat (Between $ 0 `And` (fromIntegral $ 6 - lenBs1)) $ takeAWord16 <* skipColon
    _ <- optional skipColon
    is <- format 6 bs1 bs2
    case is of
        [i1,i2,i3,i4,i5,i6] -> do
            m1 <- takeAWord8 <* skipDot
            m2 <- takeAWord8 <* skipDot
            m3 <- takeAWord8 <* skipDot
            m4 <- takeAWord8
            return $ fromTuple ( i1,i2,i3,i4,i5,i6
                               , m1 `shiftL` 8 .|. m2
                               , m3 `shiftL` 8 .|. m4
                               )
        _ -> error "internal error: format should return 6"

-- | IPv6 parser as described in RFC4291 section 2.2.2
--
-- The use of "::" indicates one or more groups of 16 bits of zeros.
-- The "::" can only appear once in an address.  The "::" can also be
-- used to compress leading or trailing zeros in an address.
--
-- * `2001:DB8::8:800:200C:417A`
-- * `FF01::101`
-- * `::1`
-- * `::`
--
ipv6ParserCompressed :: (ParserSource input, Element input ~ Char, Element (Chunk input) ~ Char)
                     => Parser input IPv6
ipv6ParserCompressed = do
    bs1 <- repeat (Between $ 0 `And` 8) $ takeAWord16 <* skipColon
    when (null bs1) skipColon
    let (CountOf bs1Len) = length bs1
    bs2 <- repeat (Between $ 0 `And` fromIntegral (8 - bs1Len)) $
              skipColon *> takeAWord16
    is <- format 8 bs1 bs2
    case is of
        [i1,i2,i3,i4,i5,i6,i7,i8] -> pure $ fromTuple (i1,i2,i3,i4,i5,i6,i7,i8)
        _ -> error "internal error: format should return 8"

format :: (Integral a, Monad m) => CountOf a -> [a] -> [a] -> m [a]
format sz bs1 bs2
    | sz <= (length bs1 + length bs2) = error "invalid compressed IPv6 addressed"
    | otherwise = do
        let len = sz `sizeSub` (length bs1 + length bs2)
        return $ bs1 <> replicate len 0 <> bs2

skipColon :: (ParserSource input, Element input ~ Char, Element (Chunk input) ~ Char)
          => Parser input ()
skipColon = element ':'
skipDot :: (ParserSource input, Element input ~ Char, Element (Chunk input) ~ Char)
        => Parser input ()
skipDot = element '.'
takeAWord8 :: (ParserSource input, Element input ~ Char, Element (Chunk input) ~ Char)
           => Parser input Word16
takeAWord8 = read <$> repeat (Between $ 1 `And` 4) (satisfy_ isDigit)
takeAWord16 :: (ParserSource input, Element input ~ Char, Element (Chunk input) ~ Char)
            => Parser input Word16
takeAWord16 = do
    l <- repeat (Between $ 1 `And` 4) (satisfy_ isHexDigit)
    let lhs = readHex l
     in case lhs of
          [(w, [])] -> return w
          _ -> error "internal error: can't fall here"
