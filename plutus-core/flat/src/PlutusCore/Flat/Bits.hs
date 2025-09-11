{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}


-- |Utilities to represent and display bit sequences
module PlutusCore.Flat.Bits (
    Bits,
    toBools,
    fromBools,
    bits,
    paddedBits,
    asBytes,
    asBits,
    takeBits,
    takeAllBits,
) where
-- TODO: AsBits Class?

import Data.Bits (FiniteBits (finiteBitSize), testBit)
import Data.ByteString qualified as B
import Data.Vector.Unboxed qualified as V
import Data.Word (Word8)
import PlutusCore.Flat.Class (Flat)
import PlutusCore.Flat.Decoder (Decoded)
import PlutusCore.Flat.Filler (PostAligned (PostAligned), fillerLength)
import PlutusCore.Flat.Run (flat, unflatRaw)
import Text.PrettyPrint.HughesPJClass (Doc, Pretty (pPrint), hsep, text)

-- |A sequence of bits
type Bits = V.Vector Bool

toBools :: Bits -> [Bool]
toBools = V.toList

fromBools :: [Bool] -> Bits
fromBools = V.fromList

{- $setup
>>> import Data.Word
>>> import PlutusCore.Flat.Instances.Base
>>> import PlutusCore.Flat.Instances.Test(tst,prettyShow)
-}

{- |The sequence of bits corresponding to the serialization of the passed value (without any final byte padding)

>>> bits True
[True]
-}
bits :: forall a. Flat a => a -> Bits
bits v =
    let lbs = flat v
    in case unflatRaw lbs :: Decoded (PostAligned a) of
            Right (PostAligned _ f) -> takeBits (8 * B.length lbs - fillerLength f) lbs
            Left _ -> error "incorrect coding or decoding, please inform the maintainer of this package"

{- |The sequence of bits corresponding to the byte-padded serialization of the passed value

>>> paddedBits True
[True,False,False,False,False,False,False,True]
-}
paddedBits :: forall a. Flat a => a -> Bits
paddedBits v = let lbs = flat v in takeAllBits lbs

takeAllBits :: B.ByteString -> Bits
takeAllBits lbs= takeBits (8 * B.length lbs) lbs

takeBits :: Int -> B.ByteString -> Bits
takeBits numBits lbs =
    V.generate
        (fromIntegral numBits)
        ( \n ->
            let (bb, b) = n `divMod` 8
             in testBit (B.index lbs (fromIntegral bb)) (7 - b)
        )

{- |Convert an integral value to its equivalent bit representation

>>> asBits (5::Word8)
[False,False,False,False,False,True,False,True]
-}
asBits :: FiniteBits a => a -> Bits
asBits w = let s = finiteBitSize w in V.generate s (testBit w . (s - 1 -))

{- |Convert a sequence of bits to the corresponding list of bytes

>>> asBytes $ asBits (256+3::Word16)
[1,3]
-}
asBytes :: Bits -> [Word8]
asBytes = map byteVal . bytes . V.toList

-- |Convert to the corresponding value (most significant bit first)
byteVal :: [Bool] -> Word8
byteVal = sum . zipWith (\ e b -> (if b then e else 0)) ([2 ^ n | n <- [7 :: Int, 6 .. 0]])

-- |Split a list in groups of 8 elements or less
bytes :: [t] -> [[t]]
bytes [] = []
bytes l  = let (w, r) = splitAt 8 l in w : bytes r

{- |
>>> prettyShow $ asBits (256+3::Word16)
"00000001 00000011"
-}
instance Pretty Bits where
    pPrint = hsep . map prettyBits . bytes . V.toList

prettyBits :: Foldable t => t Bool -> Doc
prettyBits l =
    text . take (length l) . concatMap (\b -> if b then "1" else "0") $ l
