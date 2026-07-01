{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.Crypto.BLS12_381.Pairing
  ( MlResult (..)
  , millerLoop
  , mulMlResult
  , finalVerify
  , mlResultMemSizeBytes
  , identityMlResult
  ) where

import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.Pretty.PrettyConst (ConstConfig)
import Text.PrettyBy (PrettyBy, prettyBy)

import Control.DeepSeq (NFData, rnf)
import Data.Hashable
import PlutusCore.Flat
import Prettyprinter

#ifdef WITH_CRYPTO
import Cardano.Crypto.EllipticCurve.BLS12_381 qualified as BlstBindings
import Cardano.Crypto.EllipticCurve.BLS12_381.Internal qualified as BlstBindings.Internal
import Data.Coerce (coerce)
#else
import Data.ByteString (ByteString)
import PlutusCore.Crypto.Utils (cryptoDisabled)
#endif

{-| This type represents the result of computing a pairing using the Miller
   loop.  Values of this type are ephemeral, only created during script
   execution.  We do not provide any means of serialising, deserialising,
   printing, or parsing MlResult values. -}
#ifdef WITH_CRYPTO
newtype MlResult = MlResult {unMlResult :: BlstBindings.PT}
  deriving newtype (Eq)
#else
-- See Note [The with-crypto flag] in PlutusCore.Crypto.Utils. MlResult values
-- are only ever created during evaluation, which is unavailable in a C-free
-- build, so the representation is a placeholder.
newtype MlResult = MlResult {unMlResult :: ByteString}
  deriving newtype (Eq)
#endif

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
  -- This might happen on the chain, so `fail` rather than `error`.
  decode = fail "Flat decoding is not supported for objects of type bls12_381_mlresult"

  -- This will be a Haskell runtime error, but encoding doesn't happen on chain,
  -- so it's not too bad.
  encode = error "Flat encoding is not supported for objects of type bls12_381_mlresult"
  size _ = id
instance NFData MlResult where
  rnf _ = ()

instance Hashable MlResult where
  hashWithSalt salt _MlResult = salt

-- | Memory usage of an MlResult point (576 bytes)
mlResultMemSizeBytes :: Int

#ifdef WITH_CRYPTO

millerLoop :: G1.Element -> G2.Element -> MlResult
millerLoop = coerce BlstBindings.millerLoop

mulMlResult :: MlResult -> MlResult -> MlResult
mulMlResult = coerce BlstBindings.ptMult

finalVerify :: MlResult -> MlResult -> Bool
finalVerify = coerce BlstBindings.ptFinalVerify

-- Not exposed as builtins

mlResultMemSizeBytes = BlstBindings.Internal.sizePT

{-| For some of the tests we need a small element of the MlResult type.  We can
get the identity element by pairing the zero elements of G1 and G2. -}
identityMlResult :: MlResult
identityMlResult = millerLoop G1.offchain_zero G2.offchain_zero

#else

-- C-free stubs. See Note [The with-crypto flag] in PlutusCore.Crypto.Utils.

millerLoop :: G1.Element -> G2.Element -> MlResult
millerLoop = cryptoDisabled "bls12_381_millerLoop"

mulMlResult :: MlResult -> MlResult -> MlResult
mulMlResult = cryptoDisabled "bls12_381_mulMlResult"

finalVerify :: MlResult -> MlResult -> Bool
finalVerify = cryptoDisabled "bls12_381_finalVerify"

mlResultMemSizeBytes = 576

identityMlResult :: MlResult
identityMlResult = cryptoDisabled "bls12_381 identityMlResult"

#endif
