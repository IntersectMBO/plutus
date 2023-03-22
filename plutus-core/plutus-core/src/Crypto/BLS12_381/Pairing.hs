{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
module Crypto.BLS12_381.Pairing
    (
     MlResult (..),
     millerLoop,
     mulMlResult,
     finalVerify,
     mlResultMemSizeBytes
    ) where

import Crypto.External.EllipticCurve.BLS12_381 qualified as BlstBindings
import Crypto.External.EllipticCurve.BLS12_381.Internal qualified as BlstBindings.Internal

import Crypto.BLS12_381.G1 qualified as G1
import Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Pretty.PrettyConst (ConstConfig)
import Text.PrettyBy (PrettyBy, prettyBy)

import Control.DeepSeq (NFData, rnf)
import Data.Bifunctor (second)
import Flat
import Prettyprinter

{- | This type reperesents the result of computing a pairing.  Values of this type
   are ephemeral, only created during script execution.  We do not provide any
   means of serialising, deserialising, printing, or parsing MlResult values. -}
newtype MlResult = MlResult { unMlResult :: BlstBindings.PT }
    deriving newtype (Eq)
instance Show MlResult where
    show _ = "<opaque>"
instance Pretty MlResult where
    pretty = pretty . show
instance PrettyBy ConstConfig MlResult where
    prettyBy _ = pretty
-- We need a Flat instance to get everything to build properly, but we'll never
-- want MlResult values in serialised scripts, so the decoding and encoding
-- functions just raise errors.
instance Flat MlResult where
    decode = fail "BLS12_381.Pairing.MlResult: flat decoding disallowed"
    encode = error "BLS12_381.Pairing.MlResult: flat encoding disallowed"
    size _ = id
instance NFData MlResult where
    rnf _ = ()

-- FIXME!!!
-- Fix this to return something more sensible and maybe log the error in the Left case
millerLoop :: G1.Element -> G2.Element -> Either BlstBindings.BLSTError MlResult
millerLoop (G1.Element e1) (G2.Element e2) = second MlResult $ BlstBindings.millerLoop e1 e2

mulMlResult :: MlResult -> MlResult -> MlResult
mulMlResult (MlResult a) (MlResult b) = MlResult $ BlstBindings.ptMult a b

finalVerify :: MlResult -> MlResult -> Bool
finalVerify (MlResult a) (MlResult b) = BlstBindings.ptFinalVerify a b


-- Not exposed as a builtin

-- | Memory usage of an MlResult point (576 bytes)
mlResultMemSizeBytes :: Int
mlResultMemSizeBytes = BlstBindings.Internal.sizePT

