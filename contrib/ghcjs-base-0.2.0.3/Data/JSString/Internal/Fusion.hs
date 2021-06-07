{-# LANGUAGE BangPatterns, MagicHash, ForeignFunctionInterface, JavaScriptFFI,
             UnliftedFFITypes
  #-}
module Data.JSString.Internal.Fusion ( -- * Types
                                       Stream(..)
                                     , Step(..)

                                       -- * Creation and elimination
                                     , stream
                                     , unstream
                                     , reverseStream

                                     , length

                                       -- * Transformations
                                     , reverse
                                       
                                       -- * Construction
                                       -- ** Scans
                                     , reverseScanr

                                       -- ** Accumulating maps
                                     , mapAccumL

                                       -- ** Generation and unfolding
                                     , unfoldrN

                                       -- * Indexing
                                     , index
                                     , findIndex
                                     , countChar
                                     ) where

import           GHC.Exts (Char(..), Int(..), chr#, Int#, isTrue#, (-#), (+#), (>=#))

import           Prelude hiding (length, reverse)
import           Data.Char

import           Data.JSString.Internal.Type (JSString(..))
import qualified Data.JSString.Internal.Type          as I
import           Data.JSString.Internal.Fusion.Types
import qualified Data.JSString.Internal.Fusion.Common as S

import           System.IO.Unsafe

import           GHCJS.Prim

default (Int)

-- | /O(n)/ Convert a 'JSString' into a 'Stream Char'.
stream :: JSString -> Stream Char
stream x = 
  let next i = case js_index i x of
                 -1#  -> Done
                 ch   -> let !i' = i + if isTrue# (ch >=# 0x10000#)
                                       then 2
                                       else 1
                         in  Yield (C# (chr# ch)) i'
  in Stream next 0
{-# INLINE [0] stream #-}

-- | /O(n)/ Convert a 'JSString' into a 'Stream Char', but iterate
-- backwards.
reverseStream :: JSString -> Stream Char
reverseStream x =
  let l = js_length x
      {-# INLINE next #-}
      next i = case js_indexR i x of
                  -1#  -> Done
                  ch   -> let !i' = i - if isTrue# (ch >=# 0x10000#)
                                        then 2
                                        else 1
                          in  Yield (C# (chr# ch)) i'
  in Stream next (I# (l -# 1#))
{-# INLINE [0] reverseStream #-}

-- | /O(n)/ Convert a 'Stream Char' into a 'JSString'.
unstream :: Stream Char -> JSString
unstream (Stream next s) = runJSString $ \done ->
  let go !s0 = case next s0 of
                 Done       -> done I.empty
                 Skip s1    -> go s1
                 Yield x s1 -> js_newSingletonArray x >>= loop 1 s1
      loop !i !s0 a = case next s0 of
                        Done       -> js_packString a >>= done
                        Skip s1    -> loop i s1 a
                        Yield x s1 -> js_writeArray x i a >> loop (i+1) s1 a
  in go s
{-# INLINE [0] unstream #-}
{-# RULES "STREAM stream/unstream fusion" forall s. stream (unstream s) = s #-}


-- ----------------------------------------------------------------------------
-- * Basic stream functions

runJSString :: ((a -> IO a) -> IO a) -> a
runJSString f = unsafePerformIO (f pure)

length :: Stream Char -> Int
length = S.lengthI
{-# INLINE[0] length #-}

-- | /O(n)/ Reverse the characters of a string.
reverse :: Stream Char -> JSString
reverse (Stream next s) = runJSString $ \done ->
  let go !s0 = case next s0 of
                 Done       -> done I.empty
                 Skip s1    -> go s1
                 Yield x s1 -> js_newSingletonArray x >>= loop 1 s1
      loop !i !s0 a = case next s0 of
                        Done       -> js_packReverse a >>= done
                        Skip s1    -> loop i s1 a
                        Yield x s1 -> js_writeArray x i a >> loop (i+1) s1 a
  in go s
{-# INLINE [0] reverse #-}

-- | /O(n)/ Perform the equivalent of 'scanr' over a list, only with
-- the input and result reversed.
reverseScanr :: (Char -> Char -> Char) -> Char -> Stream Char -> Stream Char
reverseScanr f z0 (Stream next0 s0) = Stream next (S1 :*: z0 :*: s0)
  where
    {-# INLINE next #-}
    next (S1 :*: z :*: s) = Yield z (S2 :*: z :*: s)
    next (S2 :*: z :*: s) = case next0 s of
                              Yield x s' -> let !x' = f x z
                                            in Yield x' (S2 :*: x' :*: s')
                              Skip s'    -> Skip (S2 :*: z :*: s')
                              Done       -> Done
{-# INLINE reverseScanr #-}

-- | /O(n)/ Like 'unfoldr', 'unfoldrN' builds a stream from a seed
-- value. However, the length of the result is limited by the
-- first argument to 'unfoldrN'. This function is more efficient than
-- 'unfoldr' when the length of the result is known.
unfoldrN :: Int -> (a -> Maybe (Char,a)) -> a -> Stream Char
unfoldrN n = S.unfoldrNI n
{-# INLINE [0] unfoldrN #-}

-------------------------------------------------------------------------------
-- ** Indexing streams

-- | /O(n)/ stream index (subscript) operator, starting from 0.
index :: Stream Char -> Int -> Char
index = S.indexI
{-# INLINE [0] index #-}

-- | The 'findIndex' function takes a predicate and a stream and
-- returns the index of the first element in the stream
-- satisfying the predicate.
findIndex :: (Char -> Bool) -> Stream Char -> Maybe Int
findIndex = S.findIndexI
{-# INLINE [0] findIndex #-}

-- | /O(n)/ The 'count' function returns the number of times the query
-- element appears in the given stream.
countChar :: Char -> Stream Char -> Int
countChar = S.countCharI
{-# INLINE [0] countChar #-}

-- | /O(n)/ Like a combination of 'map' and 'foldl''. Applies a
-- function to each element of a 'Text', passing an accumulating
-- parameter from left to right, and returns a final 'JSString'.
mapAccumL :: (a -> Char -> (a, Char)) -> a -> Stream Char -> (a, JSString)
mapAccumL f z0 (Stream next s0) = runJSString $ \done ->
  let go !s1 = case next s1 of
                 Done        -> done (z0, I.empty)
                 Skip s2     -> go s2
                 Yield ch s2 -> let (z1, ch1) = f z0 ch
                                in  js_newSingletonArray ch1 >>= loop 1 s2 z1
      loop !i !s1 !z1 a = case next s1 of
        Done         -> js_packString a >>= \s -> done (z1, s)
        Skip s2      -> loop i s2 z1 a
        Yield ch1 s2 -> let (z2, ch2) = f z1 ch1
                        in  js_writeArray ch2 i a >> loop (i+1) s2 z2 a
  in go s0
{-# INLINE [0] mapAccumL #-}

-------------------------------------------------------------------------------

-- returns -1 for end of stream
foreign import javascript unsafe
  "h$jsstringIndex" js_index :: Int -> JSString -> Int#
foreign import javascript unsafe
  "h$jsstringIndexR" js_indexR :: Int -> JSString -> Int#
foreign import javascript unsafe
  "$1.length" js_length :: JSString -> Int#
foreign import javascript unsafe
  "$r = [$1];" js_newSingletonArray :: Char -> IO JSVal
foreign import javascript unsafe
  "$3[$2] = $1;" js_writeArray :: Char -> Int -> JSVal -> IO ()
foreign import javascript unsafe
  "h$jsstringPackArray" js_packString :: JSVal -> IO JSString
foreign import javascript unsafe
  "h$jsstringPackArrayReverse" js_packReverse :: JSVal -> IO JSString
