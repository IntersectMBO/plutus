{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.V1.Crypto () where

import Data.Coerce (coerce)
import PlutusLedgerApi.Test.Orphans.PlutusTx (Blake2b244Hash (Blake2b244Hash))
import PlutusLedgerApi.V1.Crypto (PubKeyHash (PubKeyHash))
import Test.QuickCheck (Arbitrary, CoArbitrary, Function (function), functionMap)

-- | BLAKE2b-244 hash. This does not shrink.
deriving via Blake2b244Hash instance Arbitrary PubKeyHash

deriving via Blake2b244Hash instance CoArbitrary PubKeyHash

instance Function PubKeyHash where
  {-# INLINEABLE function #-}
  function = functionMap coerce PubKeyHash
