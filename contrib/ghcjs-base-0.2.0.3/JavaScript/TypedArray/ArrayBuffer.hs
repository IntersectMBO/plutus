module JavaScript.TypedArray.ArrayBuffer
    ( ArrayBuffer
    , MutableArrayBuffer
    , freeze, unsafeFreeze
    , thaw, unsafeThaw
    , byteLength
    ) where

import JavaScript.TypedArray.ArrayBuffer.Internal

import GHC.Exts
import GHC.Types

create :: Int -> IO MutableArrayBuffer
create n = fmap SomeArrayBuffer (IO (js_create n))
{-# INLINE create #-}

{- | Create an immutable 'ArrayBuffer' by copying a 'MutableArrayBuffer' -}
freeze :: MutableArrayBuffer -> IO ArrayBuffer
freeze (SomeArrayBuffer b) = fmap SomeArrayBuffer (IO (js_slice1 0 b))
{-# INLINE freeze #-}

{- | Create an immutable 'ArrayBuffer' from a 'MutableArrayBuffer' without
     copying. The result shares the buffer with the argument,  not modify
     the data in the 'MutableArrayBuffer' after freezing
 -}
unsafeFreeze :: MutableArrayBuffer -> IO ArrayBuffer
unsafeFreeze (SomeArrayBuffer b) = pure (SomeArrayBuffer b)
{-# INLINE unsafeFreeze #-}

{- | Create a 'MutableArrayBuffer' by copying an immutable 'ArrayBuffer' -}
thaw :: ArrayBuffer -> IO MutableArrayBuffer
thaw (SomeArrayBuffer b) = fmap SomeArrayBuffer (IO (js_slice1 0 b))
{-# INLINE thaw #-}

unsafeThaw :: ArrayBuffer -> IO MutableArrayBuffer
unsafeThaw (SomeArrayBuffer b) = pure (SomeArrayBuffer b)
{-# INLINE unsafeThaw #-}

slice :: Int -> Maybe Int -> SomeArrayBuffer any -> SomeArrayBuffer any
slice begin (Just end) b = js_slice_imm begin end b
slice begin _          b = js_slice1_imm begin b
{-# INLINE slice #-}

byteLength :: SomeArrayBuffer any -> Int
byteLength b = js_byteLength b
{-# INLINE byteLength #-}

