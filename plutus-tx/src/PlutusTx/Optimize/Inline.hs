{-# LANGUAGE CPP #-}
#if !MIN_VERSION_base(4, 15, 0)
{-# OPTIONS_GHC -Wwarn=unrecognised-pragmas #-}
#endif

module PlutusTx.Optimize.Inline (inline) where

import Prelude

-- | Like @GHC.Magic.Inline@, this function can be used to perform callsite inlining.
--
-- @inline f@ or @inline (f x1 ... xn)@ inlines @f@, as long as @f@'s unfolding is available,
-- and @f@ is not recursive.
inline :: a -> a
inline = id
{-# OPAQUE inline #-}
