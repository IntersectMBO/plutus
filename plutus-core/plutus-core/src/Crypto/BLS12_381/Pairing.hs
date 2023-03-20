{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
module Crypto.BLS12_381.Pairing
    (
     MlResult (..),
     mulMlResult,
     pairing,
     finalVerify
    ) where

import Crypto.External.EllipticCurve.BLS12_381 qualified as BlstBindings

import Crypto.BLS12_381.G1 qualified as G1
import Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Pretty.PrettyConst (ConstConfig)
import Text.PrettyBy (PrettyBy, prettyBy)

import Control.DeepSeq (NFData, rnf)
import Data.Bifunctor (second)
import Flat
import Prettyprinter

-- FIXME: maybe we don't need the newtype.
newtype MlResult = MlResult { unMlResult :: BlstBindings.PT }
    deriving newtype (Eq)
instance Show MlResult where
    show _ = "<opaque>"
instance Pretty MlResult where
    pretty = pretty . show
instance PrettyBy ConstConfig MlResult where
    prettyBy _ = pretty
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
mulMlResult (MlResult a) (MlResult b) = MlResult $ BlstBindings.ptMult a b

-- Fix this to return something more sensible and maybe log the error in the Left case
pairing :: G1.Element -> G2.Element -> Either BlstBindings.BLSTError MlResult
pairing (G1.Element e1) (G2.Element e2) = second MlResult $ BlstBindings.millerLoop e1 e2

finalVerify :: MlResult -> MlResult -> Bool
finalVerify (MlResult a) (MlResult b) = BlstBindings.ptFinalVerify a b
