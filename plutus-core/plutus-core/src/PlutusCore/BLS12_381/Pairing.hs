{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE TypeApplications #-}
module PlutusCore.BLS12_381.Pairing
    (
     MlResult (..),
     mulMlResult,
     pairing,
     finalVerify
    ) where

import Crypto.EllipticCurve.BLS12_381 qualified as BLS12_381

import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2

import Control.DeepSeq (NFData, rnf)
import Data.Bifunctor (second)
import Flat
import Prettyprinter

-- FIXME: maybe we don't need the newtype.
newtype MlResult = MlResult { unMlResult :: BLS12_381.PT }
    deriving newtype (Eq)
instance Show MlResult where
    show _ = "<opaque>"
instance Pretty MlResult where
    pretty = pretty . show
-- !! FIXME. We need a Flat instance to get everything to build properly, but
-- we'll never want GT values in serialised scripts.  Is the instance below OK?
-- Also, do we need a tag for GT in Universe.hs?
instance Flat MlResult where
    decode = fail "BLS12_381.Pairing.MlResult: flat decoding disallowed"
    encode = error "BLS12_381.Pairing.MlResult: flat encoding disallowed"
    size _ = id
instance NFData MlResult where
    rnf _ = ()

mulMlResult :: MlResult -> MlResult -> MlResult
mulMlResult (MlResult a) (MlResult b) = MlResult $ BLS12_381.ptMult a b

-- Fix this to return something more sensible and maybe log the error in the Left case
pairing :: G1.Element -> G2.Element -> Either BLS12_381.BLSTError MlResult
pairing (G1.Element e1) (G2.Element e2) = second MlResult $ BLS12_381.miller_loop e1 e2

finalVerify :: MlResult -> MlResult -> Bool
finalVerify (MlResult a) (MlResult b) = BLS12_381.ptFinalVerify a b
