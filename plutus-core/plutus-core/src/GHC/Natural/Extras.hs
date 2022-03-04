{-# LANGUAGE CPP #-}
#include "MachDeps.h"

module GHC.Natural.Extras (naturalToWord64Maybe, Natural (..)) where

import Data.IntCast (intCastEq)
import Data.Word (Word64)
import GHC.Natural

-- Note this will only work on 64bit platforms, but that's all we build on
-- so that's okay.
{-# INLINABLE naturalToWord64Maybe #-}
naturalToWord64Maybe :: Natural -> Maybe Word64
naturalToWord64Maybe n = intCastEq <$> naturalToWordMaybe n
