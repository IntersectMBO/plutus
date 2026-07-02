module PlutusCore.Crypto.BLS12_381.Error
where

import Data.Bits (testBit)
import Data.ByteString qualified as BS

data BLS12_381_Error
  = HashToCurveDstTooBig -- DSTs can be at most 255 bytes long.
  | BadCompressedData -- A compressed point failed structural (length/flag) validation.
  deriving stock (Show)

{-| Structural validation of a compressed BLS12-381 point, shared by the C-free
G1 and G2 `uncompress` stubs (@expectedLen@ is 48 for G1, 96 for G2). It checks
exactly what can be checked without field arithmetic: the length, and the three
metadata bits of the leading byte -- the compression bit must be set, and if the
infinity bit is set the encoding must be the canonical @0xc0 00..00@. It
deliberately does NOT verify that the bytes encode a point on the curve or in the
subgroup (that needs blst), so it is weaker than the real `blsUncompress`; but it
rejects the malformed inputs the real decoder rejects on structure alone, rather
than accepting anything. -}
checkCompressed :: Int -> BS.ByteString -> Either BLS12_381_Error BS.ByteString
checkCompressed expectedLen bs
  | BS.length bs /= expectedLen = Left BadCompressedData
  | not (testBit b0 7)          = Left BadCompressedData -- must be the compressed form
  | testBit b0 6                = -- point at infinity: must be exactly 0xc0 00..00
      if b0 == 0xc0 && BS.all (== 0) (BS.drop 1 bs)
        then Right bs
        else Left BadCompressedData
  | otherwise                   = Right bs
  where
    b0 = BS.head bs
