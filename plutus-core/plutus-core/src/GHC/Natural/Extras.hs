{-# LANGUAGE CPP #-}
#include "MachDeps.h"

module GHC.Natural.Extras (naturalToWord64Maybe, Natural (..)) where

import Data.Word (Word64)
import GHC.Natural

-- | Note that we only support 64-bit architectures.
-- The implementation is safe w.r.t. cross-compilation, because WORD_SIZE_IN_BITS will point
-- to the compiler's target word size when compiling this module.
{-# INLINABLE naturalToWord64Maybe #-}
naturalToWord64Maybe :: Natural -> Maybe Word64
naturalToWord64Maybe n =
#if WORD_SIZE_IN_BITS == 64
    fromIntegral <$> naturalToWordMaybe n
#else

-- hlint (or cpphs?) has problems parsing the #error cpp directive. Skip hlint then.
#ifndef __HLINT__
#error unsupported WORD_SIZE_IN_BITS. We only support 64-bit architectures.
#endif

#endif
