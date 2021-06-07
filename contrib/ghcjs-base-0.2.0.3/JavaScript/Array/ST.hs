{-# LANGUAGE Rank2Types, UnboxedTuples, MagicHash #-}

module JavaScript.Array.ST
    ( STJSArray
    , build
    , create
    , length
    , null
    , append
    , fromList
    , toList
    , read
    , write
    , push
    , pop
    , unshift
    , shift
    , reverse
    , take
    , drop
    , freeze
    , unsafeFreeze
    ) where

import qualified JavaScript.Array.Internal as I
import           JavaScript.Array.Internal (SomeJSArray(..), JSArray, STJSArray)

import Prelude hiding (length, null, read, take, drop, reverse)
import GHC.ST

import GHCJS.Types
import Unsafe.Coerce
import Control.DeepSeq

build :: (forall s. STJSArray s -> ST s ()) -> JSArray
build m = runST $ do
  a <- create
  m a
  unsafeFreeze a
{-# INLINE build #-}

create :: ST s (STJSArray s)
create = ST I.js_create
{-# INLINE create #-}

length :: STJSArray s -> ST s Int
length x = ST (I.js_length x)
{-# INLINE length #-}

null :: STJSArray s -> ST s Bool
null = fmap (==0) . length
{-# INLINE null #-}

append :: STJSArray s -> STJSArray s -> ST s (STJSArray s)
append x y = ST (I.js_append x y)
{-# INLINE append #-}

fromList :: [JSVal] -> ST s (STJSArray s)
fromList xs = ST (\s -> rnf xs `seq` I.js_toJSArray (unsafeCoerce xs) s)
{-# INLINE fromList #-}

toList :: STJSArray s -> ST s [JSVal]
toList x = ST (unsafeCoerce (I.js_fromJSArray x))
{-# INLINE toList #-}

read :: Int -> STJSArray s -> ST s (JSVal)
read n x = ST (I.js_index n x)
{-# INLINE read #-}

write :: Int -> JSVal -> STJSArray s -> ST s ()
write n e x = ST (I.js_setIndex n e x)
{-# INLINE write #-}

push :: JSVal -> STJSArray s -> ST s ()
push e x = ST (I.js_push e x)
{-# INLINE push #-}

pop :: STJSArray s -> ST s JSVal
pop x = ST (I.js_pop x)
{-# INLINE pop #-}

unshift :: JSVal -> STJSArray s -> ST s ()
unshift e x = ST (I.js_unshift e x)
{-# INLINE unshift #-}

shift :: STJSArray s -> ST s JSVal
shift x = ST (I.js_shift x)
{-# INLINE shift #-}

reverse :: STJSArray s -> ST s ()
reverse x = ST (I.js_reverse x)
{-# INLINE reverse #-}

take :: Int -> STJSArray s -> ST s (STJSArray s)
take n x = ST (I.js_slice 0 n x)
{-# INLINE take #-}

drop :: Int -> STJSArray s -> ST s (STJSArray s)
drop n x = ST (I.js_slice1 n x)
{-# INLINE drop #-}

slice :: Int -> Int -> STJSArray s -> ST s (STJSArray s)
slice s n x = ST (I.js_slice s n x)
{-# INLINE slice #-}

freeze :: STJSArray s -> ST s JSArray
freeze x = ST (I.js_slice1 0 x)
{-# INLINE freeze #-}

unsafeFreeze :: STJSArray s -> ST s JSArray
unsafeFreeze (SomeJSArray x) = pure (SomeJSArray x)
{-# INLINE unsafeFreeze #-}
