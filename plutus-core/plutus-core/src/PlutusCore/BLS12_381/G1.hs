-- editorconfig-checker-disable
{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.BLS12_381.G1
    ( Element (..)
    , add
    , mul
    , neg
    , hashToCurve
    , compress
    , uncompress
    , zero
    ) where

-- FIXME: perhaps export the in-memory and (compressed) serialised sizes of
-- elements.  We need these in ExMemory.hs and CreateBuiltinCostModel.hs.  Can
-- we get these numbers from the library easily?

import Crypto.EllipticCurve.BLS12_381 qualified as BLS12_381
import PlutusCore.BLS12_381.Utils (byteStringAsHex)
-- import PlutusCore.Evaluation.Result
-- ^ Importing this causes a loop.

import Control.DeepSeq (NFData, rnf)
import Data.Bifunctor (second)
import Data.ByteString (ByteString, pack)
import Flat
import Prettyprinter

-- We have to wrap the BLS points in a newtype because otherwise
-- the builtin machinery seems to spot that they're applications,
-- and we don't want to expose that to users.
newtype Element = Element { unElement :: BLS12_381.P1 }
    deriving newtype (Eq)
instance Show Element where
    show  = byteStringAsHex . compress
instance Pretty Element where
    pretty = pretty . show
instance Flat Element where
    decode = do
        x <- decode
        case BLS12_381.uncompress @BLS12_381.Curve1 x of
             Left err -> fail $ show err
             Right e  -> pure $ Element e
    encode = encode . BLS12_381.compress @BLS12_381.Curve1 . unElement
    size = size . compress
instance NFData Element where
    rnf _ = ()

add :: Element -> Element -> Element
add (Element a) (Element b) = Element $ BLS12_381.addOrDouble @BLS12_381.Curve1 a b

mul :: Integer -> Element -> Element -- Other way round from implementation
mul k (Element a) = Element $ BLS12_381.mult @BLS12_381.Curve1 a k

neg :: Element -> Element
neg (Element a) = Element $ BLS12_381.neg @BLS12_381.Curve1 a

compress :: Element -> ByteString  -- 48 bytes
compress (Element a) = BLS12_381.compress @BLS12_381.Curve1 a

uncompress :: ByteString -> Either BLS12_381.BLSTError Element
uncompress = second Element . BLS12_381.uncompress @BLS12_381.Curve1

-- Take an arbitrary bytestring and hash it to a get point on the curve;
hashToCurve :: ByteString -> Element
hashToCurve s = Element $ BLS12_381.hash @BLS12_381.Curve1 s Nothing Nothing

-- This is only here for the QuickCheck shrinker in the PlutusIR tests.  I'm not
-- sure if it even makes sense for that.
zero :: Element
zero =
    let b = pack (0xc0 : replicate 47 0x00) -- Compressed serialised G1 points are bytestrings of length 48: see CIP-0381.
    in case BLS12_381.uncompress @BLS12_381.Curve1 b of
         Left err       -> error $ "Unexpected failure deserialising point at infinity on BLS12_381.G1:  " ++ show err
         Right infinity -> Element infinity  -- The zero point on this curve is chosen to be the point at infinity.

