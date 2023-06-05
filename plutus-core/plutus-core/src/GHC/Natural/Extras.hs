{-# LANGUAGE CPP #-}
#include "MachDeps.h"

module GHC.Natural.Extras (naturalToWord64Maybe, Natural (..)) where

import Data.Word (Word64)
import GHC.Natural

{- | We only support 64-bit architectures, see Note [Index (Word64) (de)serialized through Natural].
This implementation is safe w.r.t. cross-compilation, because WORD_SIZE_IN_BITS will point
to the compiler's target word size when compiling this module.
-}
{-# INLINABLE naturalToWord64Maybe #-}
naturalToWord64Maybe :: Natural -> Maybe Word64
naturalToWord64Maybe n =
#if WORD_SIZE_IN_BITS == 64
    fromIntegral <$> naturalToWordMaybe n
#else

{- HLint does not know about WORD_SIZE_IN_BITS, so it calls cpphs to preprocess away these lines;
cpphs fails on encountering the #error cpp directive (as it should).
HLint treats this cpphs failure as an hlint failure. Skip HLint then.
-}
#ifndef __HLINT__
#error unsupported WORD_SIZE_IN_BITS. We only support 64-bit architectures.
#endif

#endif
