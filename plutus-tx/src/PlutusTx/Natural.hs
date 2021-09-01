-- | An on-chain numeric type representing non-negative integers.
module PlutusTx.Natural (
  -- * Types,
  Internal.Natural (..),
  Internal.Parity (..),

  -- * Quasi-quoter
  TH.nat,

  -- * Functions
  Internal.parity,
  Internal.powNat,
  (Internal.^+),
  (Internal.^-)
) where

import qualified PlutusTx.Natural.Internal as Internal
import qualified PlutusTx.Natural.TH       as TH
