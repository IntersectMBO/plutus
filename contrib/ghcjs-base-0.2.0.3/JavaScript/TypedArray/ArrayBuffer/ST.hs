module JavaScript.TypedArray.ArrayBuffer.ST
    ( STArrayBuffer
    , freeze, unsafeFreeze
    , thaw, unsafeThaw
    ) where

import Control.Monad.ST

import GHC.Types
import GHC.Exts
import GHC.ST

import JavaScript.TypedArray.ArrayBuffer.Internal

create :: Int -> ST s (STArrayBuffer s)
create n = fmap SomeArrayBuffer $ ST (js_create n)
{-# INLINE create #-}

freeze :: STArrayBuffer s -> ST s ArrayBuffer
freeze (SomeArrayBuffer b) = fmap SomeArrayBuffer (ST (js_slice1 0 b))
{-# INLINE freeze #-}

unsafeFreeze :: STArrayBuffer s -> ST s ArrayBuffer
unsafeFreeze (SomeArrayBuffer b) = pure (SomeArrayBuffer b)
{-# INLINE unsafeFreeze #-}

{- | Create an 'STArrayBuffer' by copying an immutable 'ArrayBuffer' -}
thaw :: ArrayBuffer -> ST s (STArrayBuffer s)
thaw (SomeArrayBuffer b) = fmap SomeArrayBuffer (ST (js_slice1 0 b))
{-# INLINE thaw #-}

unsafeThaw :: ArrayBuffer -> ST s (STArrayBuffer s)
unsafeThaw (SomeArrayBuffer b) = pure (SomeArrayBuffer b)
{-# INLINE unsafeThaw #-}

