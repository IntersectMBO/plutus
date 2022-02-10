{-# LANGUAGE CPP #-}
#include "MachDeps.h"

module GHC.Natural.Extras (naturalToWord64Maybe, Natural (..)) where

import Data.Word (Word64)
import GHC.Natural

{-# INLINABLE naturalToWord64Maybe #-}
naturalToWord64Maybe :: Natural -> Maybe Word64
naturalToWord64Maybe n =
#if WORD_SIZE_IN_BITS == 64
    fromIntegral <$> naturalToWordMaybe n
#else
     if n <= (fromIntegral (maxBound :: Word64) :: Natural)
     then Just $ fromIntegral n
     else Nothing
#endif
