{-# LANGUAGE DerivingVia #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.V1.Time () where

import Data.Coerce (coerce)
import PlutusLedgerApi.V1.Time (POSIXTime (POSIXTime))
import Test.QuickCheck (Arbitrary, CoArbitrary, Function (function), functionMap)

deriving via Integer instance Arbitrary POSIXTime

deriving via Integer instance CoArbitrary POSIXTime

instance Function POSIXTime where
  {-# INLINEABLE function #-}
  function = functionMap coerce POSIXTime
