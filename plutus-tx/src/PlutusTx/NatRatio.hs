-- | An on-chain numeric type representing a ratio of non-negative numbers.
module PlutusTx.NatRatio
  ( -- * Type
    Internal.NatRatio

  , -- * Functions

    -- ** Construction
    Internal.fromNatural
  , Internal.natRatio
  , TH.nr

  , -- ** Access
    Internal.numerator
  , Internal.denominator
  , Internal.truncate
  , Internal.round
  , Internal.properFraction
  ) where

import qualified PlutusTx.NatRatio.Internal as Internal
import qualified PlutusTx.NatRatio.TH       as TH
