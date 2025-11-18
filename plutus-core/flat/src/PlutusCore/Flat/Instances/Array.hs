{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Flat instances for the `array` package
module PlutusCore.Flat.Instances.Array ()
where

import Data.Array qualified as A
import Data.Array.IArray
import Data.Array.Unboxed qualified as U
import PlutusCore.Flat.Class
import PlutusCore.Flat.Decoder
import PlutusCore.Flat.Encoder
import PlutusCore.Flat.Instances.Base ()

-- import PlutusCore.Flat.Instances.Util
import PlutusCore.Flat.Instances.Mono

{-$setup
>>> :set -XFlexibleContexts
>>> import           Flat.Instances.Test
>>> import           Flat.Instances.Mono
>>> import           qualified Data.Array as A
>>> import           qualified Data.Array.Unboxed as U
>>> import           Data.Array.IArray
>>> import           Data.Word -}

{-|
Array is encoded as (lowBound,highBound,AsArray (elems array)):

>>> let arr = A.array ((1::Word,4::Word),(2,5)) [((1,4),11::Word),((1,5),22),((2,4),33),((2,5),44)] in tst (bounds arr,AsArray(elems arr)) == tst arr
True

As it's easy to see:

>>> tst $ A.array ((1::Word,4::Word),(2,5)) [((1,4),11::Word),((1,5),22),((2,4),33),((2,5),44)]
(True,80,[1,4,2,5,4,11,22,33,44,0])

>>> tst $ A.array ((1,4),(2,5)) [((1,4),"1.4"),((1,5),"1.5"),((2,4),"2.4"),((2,5),"2.5")]
(True,160,[2,8,4,10,4,152,203,166,137,140,186,106,153,75,166,137,148,186,106,0])

Arrays and Unboxed Arrays are encoded in the same way:

>>> let bounds = ((1::Word,4::Word),(2,5));elems=[11::Word,22,33,44] in tst (U.listArray bounds elems :: U.UArray (Word,Word) Word) == tst (A.listArray bounds elems)
True -}
instance (Flat i, Flat e, Ix i) => Flat (A.Array i e) where
  size = sizeIArray

  encode = encodeIArray

  decode = decodeIArray

instance (Flat i, Flat e, Ix i, IArray U.UArray e) => Flat (U.UArray i e) where
  size = sizeIArray

  encode = encodeIArray

  decode = decodeIArray

sizeIArray :: (IArray a e, Ix i, Flat e, Flat i) => a i e -> NumBits -> NumBits
sizeIArray arr = (sizeSequence . elems $ arr) . size (bounds arr)

encodeIArray :: (Ix i, IArray a e, Flat i, Flat e) => a i e -> Encoding
encodeIArray arr = encode (bounds arr) <> encodeSequence (elems arr)

decodeIArray :: (Ix i, IArray a e, Flat i, Flat e) => Get (a i e)
decodeIArray = listArray <$> decode <*> decodeSequence

{-# INLINE sizeIArray #-}
{-# INLINE encodeIArray #-}
{-# INLINE decodeIArray #-}
