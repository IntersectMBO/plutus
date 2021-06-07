{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI, DataKinds, KindSignatures,
             PolyKinds, UnboxedTuples, GHCForeignImportPrim, DeriveDataTypeable,
             UnliftedFFITypes, MagicHash
  #-}
module JavaScript.Array.Internal where

import           Prelude hiding (length, reverse, drop, take)

import           Control.DeepSeq
import           Data.Typeable
import           Unsafe.Coerce (unsafeCoerce)

import           GHC.Types
import           GHC.IO
import qualified GHC.Exts as Exts
import           GHC.Exts (State#)

import           GHCJS.Internal.Types
import qualified GHCJS.Prim as Prim
import           GHCJS.Types

newtype SomeJSArray (m :: MutabilityType s) = SomeJSArray JSVal
  deriving (Typeable)
instance IsJSVal (SomeJSArray m)

type JSArray        = SomeJSArray Immutable
type MutableJSArray = SomeJSArray Mutable

type STJSArray s    = SomeJSArray (STMutable s)

create :: IO MutableJSArray
create = IO js_create
{-# INLINE create #-}

length :: JSArray -> Int
length x = js_lengthPure x
{-# INLINE length #-}

lengthIO :: SomeJSArray m -> IO Int
lengthIO x = IO (js_length x)
{-# INLINE lengthIO #-}

null :: JSArray -> Bool
null x = length x == 0
{-# INLINE null #-}

append :: SomeJSArray m -> SomeJSArray m -> IO (SomeJSArray m1)
append x y = IO (js_append x y)
{-# INLINE append #-}

fromList :: [JSVal] -> JSArray
fromList xs = rnf xs `seq` js_toJSArrayPure (unsafeCoerce xs)
{-# INLINE fromList #-}

fromListIO :: [JSVal] -> IO (SomeJSArray m)
fromListIO xs = IO (\s -> rnf xs `seq` js_toJSArray (unsafeCoerce xs) s)
{-# INLINE fromListIO #-}

toList :: JSArray -> [JSVal]
toList x = unsafeCoerce (js_fromJSArrayPure x)
{-# INLINE toList #-}

toListIO :: SomeJSArray m -> IO [JSVal]
toListIO x = IO $ \s -> case js_fromJSArray x s of
                          (# s', xs #) -> (# s', unsafeCoerce xs #)
{-# INLINE toListIO #-}

index :: Int -> JSArray -> JSVal
index n x = js_indexPure n x
{-# INLINE index #-}

read :: Int -> SomeJSArray m -> IO JSVal
read n x = IO (js_index n x)
{-# INLINE read #-}

write :: Int -> JSVal -> MutableJSArray -> IO ()
write n e x = IO (js_setIndex n e x)
{-# INLINE write #-}

push :: JSVal -> MutableJSArray -> IO ()
push e x = IO (js_push e x)
{-# INLINE push #-}

pop :: MutableJSArray -> IO JSVal
pop x = IO (js_pop x)
{-# INLINE pop #-}

unshift :: JSVal -> MutableJSArray -> IO ()
unshift e x = IO (js_unshift e x)
{-# INLINE unshift #-}

shift :: MutableJSArray -> IO JSVal
shift x = IO (js_shift x)
{-# INLINE shift #-}

reverse :: MutableJSArray -> IO ()
reverse x = IO (js_reverse x)
{-# INLINE reverse #-}

take :: Int -> JSArray -> JSArray
take n x = js_slicePure 0 n x
{-# INLINE take #-}

takeIO :: Int -> SomeJSArray m -> IO (SomeJSArray m1)
takeIO n x = IO (js_slice 0 n x)
{-# INLINE takeIO #-}

drop :: Int -> JSArray -> JSArray
drop n x = js_slice1Pure n x
{-# INLINE drop #-}

dropIO :: Int -> SomeJSArray m -> IO (SomeJSArray m1)
dropIO n x = IO (js_slice1 n x)
{-# INLINE dropIO #-}

sliceIO :: Int -> Int -> JSArray -> IO (SomeJSArray m1)
sliceIO s n x = IO (js_slice s n x)
{-# INLINE sliceIO #-}

slice :: Int -> Int -> JSArray -> JSArray
slice s n x = js_slicePure s n x
{-# INLINE slice #-}

freeze :: MutableJSArray -> IO JSArray
freeze x = IO (js_slice1 0 x)
{-# INLINE freeze #-}

unsafeFreeze :: MutableJSArray -> IO JSArray
unsafeFreeze (SomeJSArray x) = pure (SomeJSArray x)
{-# INLINE unsafeFreeze #-}

thaw :: JSArray -> IO MutableJSArray
thaw x = IO (js_slice1 0 x)
{-# INLINE thaw #-}

unsafeThaw :: JSArray -> IO MutableJSArray
unsafeThaw (SomeJSArray x) = pure (SomeJSArray x)
{-# INLINE unsafeThaw #-}


-- -----------------------------------------------------------------------------

foreign import javascript unsafe "$r = [];"
  js_create   :: State# s -> (# State# s, SomeJSArray m #)

foreign import javascript unsafe "$1.length"
  js_length     :: SomeJSArray m -> State# s -> (# State# s, Int #)
foreign import javascript unsafe "$2[$1]"
  js_index     :: Int -> SomeJSArray m -> State# s -> (# State# s, JSVal #)

foreign import javascript unsafe "$2[$1]"
  js_indexPure :: Int -> JSArray -> JSVal
foreign import javascript unsafe "$1.length"
  js_lengthPure :: JSArray -> Int

foreign import javascript unsafe "$3[$1] = $2"
  js_setIndex :: Int -> JSVal -> SomeJSArray m -> State# s -> (# State# s, () #)

foreign import javascript unsafe "$3.slice($1,$2)"
  js_slice     :: Int -> Int -> SomeJSArray m -> State# s -> (# State# s, SomeJSArray m1 #)
foreign import javascript unsafe "$2.slice($1)"
  js_slice1    :: Int -> SomeJSArray m -> State# s -> (# State# s, SomeJSArray m1 #)

foreign import javascript unsafe "$3.slice($1,2)"
  js_slicePure  :: Int -> Int -> JSArray -> JSArray
foreign import javascript unsafe "$2.slice($1)"
  js_slice1Pure :: Int -> JSArray -> JSArray

foreign import javascript unsafe "$1.concat($2)"
  js_append   :: SomeJSArray m0 -> SomeJSArray m1 -> State# s ->  (# State# s, SomeJSArray m2 #)

foreign import javascript unsafe "$2.push($1)"
  js_push     :: JSVal -> SomeJSArray m -> State# s -> (# State# s, () #)
foreign import javascript unsafe "$1.pop()"
  js_pop      :: SomeJSArray m -> State# s -> (# State# s, JSVal #)
foreign import javascript unsafe "$2.unshift($1)"
  js_unshift  :: JSVal -> SomeJSArray m -> State# s -> (# State# s, () #)
foreign import javascript unsafe "$1.shift()"
  js_shift    :: SomeJSArray m -> State# s -> (# State# s, JSVal #)

foreign import javascript unsafe "$1.reverse()"
  js_reverse  :: SomeJSArray m -> State# s -> (# State# s, () #)

foreign import javascript unsafe "h$toHsListJSVal($1)"
  js_fromJSArray :: SomeJSArray m -> State# s -> (# State# s, Exts.Any #)
foreign import javascript unsafe "h$toHsListJSVal($1)"
  js_fromJSArrayPure :: JSArray -> Exts.Any -- [JSVal]

foreign import javascript unsafe "h$fromHsListJSVal($1)"
  js_toJSArray :: Exts.Any -> State# s -> (# State# s, SomeJSArray m #)
foreign import javascript unsafe "h$fromHsListJSVal($1)"
  js_toJSArrayPure :: Exts.Any -> JSArray

