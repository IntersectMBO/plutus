{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
module PlutusCore.Crypto.BLS12_381.Pairing
    (
     MlResult (..),
     millerLoop,
     mulMlResult,
     finalVerify,
     mlResultMemSizeBytes
    ) where

import Cardano.Crypto.EllipticCurve.BLS12_381 qualified as BlstBindings
import Cardano.Crypto.EllipticCurve.BLS12_381.Internal qualified as BlstBindings.Internal

import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Pretty.PrettyConst (ConstConfig)
import Text.PrettyBy (PrettyBy, prettyBy)

import Control.DeepSeq (NFData, rnf)
import Flat
import Prettyprinter

{- | This type represents the result of computing a pairing using the Miller
   loop.  Values of this type are ephemeral, only created during script
   execution.  We do not provide any means of serialising, deserialising,
   printing, or parsing MlResult values. -}
newtype MlResult = MlResult { unMlResult :: BlstBindings.PT }
    deriving newtype (Eq)
instance Show MlResult where
    show _ = "<opaque>"
instance Pretty MlResult where
    pretty = pretty . show
instance PrettyBy ConstConfig MlResult where
    prettyBy _ = pretty
-- We need a Flat instance to get everything to build properly; however we'll
-- never want MlResult values in serialised scripts, so the decoding and
-- encoding functions just raise errors.
instance Flat MlResult where
    decode = fail "BLS12_381.Pairing.MlResult: flat decoding disallowed"
    encode = error "BLS12_381.Pairing.MlResult: flat encoding disallowed"
    size _ = id
instance NFData MlResult where
    rnf _ = ()

-- TODO: perhaps make this emit the error in the Left case.
millerLoop :: G1.Element -> G2.Element -> MlResult
millerLoop (G1.Element e1) (G2.Element e2) = MlResult $ BlstBindings.millerLoop e1 e2

mulMlResult :: MlResult -> MlResult -> MlResult
mulMlResult (MlResult a) (MlResult b) = MlResult $ BlstBindings.ptMult a b

finalVerify :: MlResult -> MlResult -> Bool
finalVerify (MlResult a) (MlResult b) = BlstBindings.ptFinalVerify a b


-- Not exposed as a builtin

-- | Memory usage of an MlResult point (576 bytes)
mlResultMemSizeBytes :: Int
mlResultMemSizeBytes = BlstBindings.Internal.sizePT

