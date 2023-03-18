-- editorconfig-checker-disable
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}

module Crypto.BLS12_381.G1
    ( Element (..)
    , add
    , neg
    , scalarMul
    , hashToGroup
    , compress
    , uncompress
    , zero
    ) where

-- FIXME: perhaps export the in-memory and (compressed) serialised sizes of
-- elements.  We need these in ExMemory.hs and CreateBuiltinCostModel.hs.  Can
-- we get these numbers from the library easily?

import Crypto.External.EllipticCurve.BLS12_381 qualified as BlstBindings

import Crypto.Utils (byteStringAsHex)
import PlutusCore.Pretty.PrettyConst (ConstConfig)
import Text.PrettyBy (PrettyBy, prettyBy)

import Control.DeepSeq (NFData, rnf)
import Data.Bifunctor (second)
import Data.ByteString (ByteString, pack)
import Flat
import Prettyprinter

-- We have to wrap the BLS points in a newtype because otherwise
-- the builtin machinery seems to spot that they're applications,
-- and we don't want to expose that to users.
newtype Element = Element { unElement :: BlstBindings.P1 }
    deriving newtype (Eq)
instance Show Element where
    show  = byteStringAsHex . compress
instance Pretty Element where
    pretty = pretty . show
instance PrettyBy ConstConfig Element where
    prettyBy _ = pretty
instance Flat Element where
    decode = do
        x <- decode
        case BlstBindings.uncompress @BlstBindings.Curve1 x of
             Left err -> fail $ show err
             Right e  -> pure $ Element e
    encode = encode . BlstBindings.compress @BlstBindings.Curve1 . unElement
    size = size . compress
instance NFData Element where
    rnf _ = ()

add :: Element -> Element -> Element
add (Element a) (Element b) = Element $ BlstBindings.addOrDouble @BlstBindings.Curve1 a b

neg :: Element -> Element
neg (Element a) = Element $ BlstBindings.neg @BlstBindings.Curve1 a

scalarMul :: Integer -> Element -> Element -- Other way round from implementation
scalarMul k (Element a) = Element $ BlstBindings.mult @BlstBindings.Curve1 a k

compress :: Element -> ByteString  -- 48 bytes
compress (Element a) = BlstBindings.compress @BlstBindings.Curve1 a

uncompress :: ByteString -> Either BlstBindings.BLSTError Element
uncompress = second Element . BlstBindings.uncompress @BlstBindings.Curve1

-- Take an arbitrary bytestring and hash it to a get point on the curve;
hashToGroup :: ByteString -> Element
hashToGroup s = Element $ BlstBindings.hash @BlstBindings.Curve1 s Nothing Nothing

-- This is only here for the QuickCheck shrinker in the PlutusIR tests.  I'm not
-- sure if it even makes sense for that.
zero :: Element
zero =
    let b = pack (0xc0 : replicate 47 0x00) -- Compressed serialised G1 points are bytestrings of length 48: see CIP-0381.
    in case BlstBindings.uncompress @BlstBindings.Curve1 b of
         Left err       -> error $ "Unexpected failure deserialising point at infinity on BLS12_381.G1:  " ++ show err
         Right infinity -> Element infinity  -- The zero point on this curve is chosen to be the point at infinity.

