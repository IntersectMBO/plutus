{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI #-}
module JavaScript.Array
    ( JSArray
    , MutableJSArray
    , create
    , length
    , lengthIO
    , null
    , fromList
    , fromListIO
    , toList
    , toListIO
    , index, (!)
    , read
    , write
    , append
    , push
    , pop
    , unshift
    , shift
    , reverse
    , take
    , takeIO
    , drop
    , dropIO
    , slice
    , sliceIO
    , freeze
    , unsafeFreeze
    , thaw
    , unsafeThaw
    ) where

import           Prelude hiding (length, drop, read, take, reverse, null)

import qualified GHCJS.Prim    as Prim
import           GHCJS.Types

import           JavaScript.Array.Internal (JSArray(..))
import           JavaScript.Array.Internal

-- import qualified JavaScript.Array.Internal as I
{-
fromList :: [JSVal] -> IO (JSArray a)
fromList xs = fmap JSArray (I.fromList xs)
{-# INLINE fromList #-}

toList :: JSArray a -> IO [JSVal]
toList (JSArray x) = I.toList x
{-# INLINE toList #-}

create :: IO (JSArray a)
create = fmap JSArray I.create
{-# INLINE create #-}

length :: JSArray a -> IO Int
length (JSArray x) = I.length x
{-# INLINE length #-}

append :: JSArray a -> JSArray a -> IO (JSArray a)
append (JSArray x) (JSArray y) = fmap JSArray (I.append x y)
{-# INLINE append #-}
-}

(!) :: JSArray -> Int -> JSVal
x ! n = index n x
{-# INLINE (!) #-}

{-

index :: Int -> JSArray a -> IO JSVal
index n (JSArray x) = I.index n x
{-# INLINE index #-}

write :: Int -> JSVal -> JSArray a -> IO ()
write n e (JSArray x) = I.write n e x
{-# INLINE write #-}

drop :: Int -> JSArray a -> IO (JSArray a)
drop n (JSArray x) = fmap JSArray (I.drop n x)
{-# INLINE drop #-}

take :: Int -> JSArray a -> IO (JSArray a)
take n (JSArray x) = fmap JSArray (I.take n x)
{-# INLINE take #-}

slice :: Int -> Int -> JSArray a -> IO (JSArray a)
slice s n (JSArray x) = fmap JSArray (I.slice s n x)
{-# INLINE slice #-}

push :: JSVal -> JSArray a -> IO ()
push e (JSArray x) = I.push e x
{-# INLINE push #-}

pop :: JSArray a -> IO JSVal
pop (JSArray x) = I.pop x
{-# INLINE pop #-}

unshift :: JSVal -> JSArray a -> IO ()
unshift e (JSArray x) = I.unshift e x
{-# INLINE unshift #-}

shift :: JSArray a -> IO JSVal
shift (JSArray x) = I.shift x
{-# INLINE shift #-}

reverse :: JSArray a -> IO ()
reverse (JSArray x) = I.reverse x
{-# INLINE reverse #-}
-}

