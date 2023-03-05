{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.BLS12_381.GT
    ( Element (..)
    , mul
    , pairing
    , finalVerify
    ) where

import Crypto.EllipticCurve.BLS12_381 qualified as BLS12_381
import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2

import Control.DeepSeq (NFData, rnf)
import Data.Bifunctor (second)
import Flat
import Prettyprinter

newtype Element = Element { unElement :: BLS12_381.PT }
    deriving newtype (Eq)
instance Show Element where
    show _ = "<opaque>"
instance Pretty Element where
    pretty = pretty . show
-- !! FIXME. We need a Flat instance to get everything to build properly, but
-- we'll never want GT values in serialised scripts.  Is the instance below OK?
-- Also, do we need a tag for GT in Universe.hs?
instance Flat Element where
    decode = fail "BLS12_381.GT.Element: flat decoding disallowed"
    encode = error "BLS12_381.GT.Element: flat encoding disallowed"
    size _ = id
instance NFData Element where
    rnf _ = ()

mul :: Element -> Element -> Element
mul (Element a) (Element b) = Element $ BLS12_381.ptMult a b

-- Fix this to return something more sensible and maybe log the error in the Left case
pairing :: G1.Element -> G2.Element -> Either BLS12_381.BLSTError Element
pairing (G1.Element e1) (G2.Element e2) = second Element $ BLS12_381.pairing e1 e2

finalVerify :: Element -> Element -> Bool
finalVerify (Element a) (Element b) = BLS12_381.ptFinalVerify a b





