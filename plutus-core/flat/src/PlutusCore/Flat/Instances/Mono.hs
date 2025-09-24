{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances      #-}

module PlutusCore.Flat.Instances.Mono
  ( sizeSequence
  , encodeSequence
  , decodeSequence
  , sizeList
  , encodeList
  , decodeList
  , sizeSet
  , encodeSet
  , decodeSet
  , sizeMap
  , encodeMap
  , decodeMap
  , AsArray(..)
  , AsList(..)
  , AsSet(..)
  , AsMap(..)
  )
where

import Data.Containers
import Data.Foldable qualified as F
import Data.MonoTraversable (Element, MonoFoldable, ofoldl', otoList)
import Data.Sequences (IsSequence)
import Data.Sequences qualified as S
import PlutusCore.Flat.Instances.Util

{- $setup
>>> import PlutusCore.Flat.Instances.Base()
>>> import PlutusCore.Flat.Instances.Test
>>> import Data.Word
>>> import qualified Data.Set
>>> import qualified Data.Map
-}

{-|
Sequences are defined as Arrays:

Array v = A0
        | A1 v (Array v)
        | A2 v v (Array v)
        ...
        | A255 ... (Array v)

In practice, this means that the sequence is encoded as a sequence of blocks of up to 255 elements, with every block preceded by the count of the elements in the block and a final 0-length block.

Lists are defined as:

List a ≡  Nil
        | Cons a (List a)

In practice, this means that the list elements will be prefixed with a 1 bit and followed by a final 0 bit.

The AsList/AsArray wrappers can be used to serialise sequences as Lists or Arrays.

Let's see some examples.

>>> flatBits $ AsList [True,True,True]
"1111110"

So we have Cons True (11) repeated three times, followed by a final Nil (0).

The list encoding is the default one for lists so AsList is in this case unnecessary:

>>> flatBits $ [True,True,True]
"1111110"

We can force a list to be encoded as an Array with AsArray:

>>> flatBits $ AsArray [True,True,True]
"00000011 11100000 000"

We have the initial block with a count of 3 (3 == 00000011) followed by the elements True True True (111) and then the final block of 0 elements ("00000 000").

>>> flatBits $ [AsArray [True,True,True]]
"10000001 11110000 00000"

>>> flatBits $ (True,True,True,AsArray $ replicate 7 True)
"11100000 11111111 11000000 00"

>>> flatBits $ AsArray ([]::[()])
"00000000"

>>> flatBits $ AsList ([]::[()])
"0"

>>> tst (AsList [11::Word8,22,33])
(True,28,[133,197,164,32])

>>> tst (AsSet (Data.Set.fromList [11::Word8,22,33]))
(True,28,[133,197,164,32])

>>> tst [AsArray [1..3], AsArray [4..8]]
(True,99,[129,129,2,3,0,65,66,2,131,3,132,0,0])

>>> tst $ [AsArray [(1::Word8)..3], AsArray [4..8]]
(True,99,[129,128,129,1,128,65,65,1,65,129,194,0,0])

>>> tst $ [AsArray [(1::Int)..3]]
(True,42,[129,129,2,3,0,0])
-}
newtype AsArray a =
  AsArray
    { unArray :: a
    } deriving (Show,Eq,Ord)

instance (IsSequence r, Flat (Element r)) => Flat (AsArray r) where
  size (AsArray a) = sizeSequence a
  encode (AsArray a) = encodeSequence a
  decode = AsArray <$> decodeSequence

{- |
Calculate size of an instance of IsSequence as the sum:

* of the size of all the elements

* plus the size of the array constructors (1 byte every 255 elements plus one final byte)
-}
sizeSequence
  :: (IsSequence mono, Flat (Element mono)) => mono -> NumBits -> NumBits
sizeSequence s acc =
  let (sz, len) =
          ofoldl' (\(acc, l) e -> (size e acc, l + 1)) (acc, 0 :: NumBits) s
  in  sz + arrayBits len
{-# INLINE sizeSequence #-}

-- TODO: check which one is faster
-- sizeSequence s acc = ofoldl' (flip size) acc s + arrayBits (olength s)

-- |Encode an instance of IsSequence, as an array
encodeSequence :: (Flat (Element mono), MonoFoldable mono) => mono -> Encoding
encodeSequence = encodeArray . otoList
{-# INLINE encodeSequence #-}

-- |Decode an instance of IsSequence, as an array
decodeSequence :: (Flat (Element b), IsSequence b) => Get b
decodeSequence = S.fromList <$> decodeArrayWith decode
{-# INLINE decodeSequence #-}

newtype AsList a =
  AsList
    { unList :: a
    } deriving (Show,Eq,Ord)

instance (IsSequence l, Flat (Element l)) => Flat (AsList l) where
  -- size   = sizeList . S.unpack . unList
  -- encode = encodeList . S.unpack . unList
  -- decode = AsList . S.fromList <$> decodeListotoList

  size   = sizeList . unList
  encode = encodeList . unList
  decode = AsList <$> decodeList

{-# INLINE sizeList #-}
sizeList
  :: (MonoFoldable mono, Flat (Element mono)) => mono -> NumBits -> NumBits
sizeList l sz = ofoldl' (\s e -> size e (s + 1)) (sz + 1) l

{-# INLINE encodeList #-}
encodeList :: (Flat (Element mono), MonoFoldable mono) => mono -> Encoding
encodeList = encodeListWith encode . otoList

{-# INLINE decodeList #-}
decodeList :: (IsSequence b, Flat (Element b)) => Get b
decodeList = S.fromList <$> decodeListWith decode

{-|
Sets are saved as lists of values.

>>> tstBits $ AsSet (Data.Set.fromList ([False,True,False]::[Bool]))
(True,5,"10110")
-}
newtype AsSet a =
  AsSet
    { unSet :: a
    } deriving (Show,Eq,Ord)

instance (IsSet set, Flat (Element set)) => Flat (AsSet set) where
  size   = sizeSet . unSet
  encode = encodeSet . unSet
  decode = AsSet <$> decodeSet

sizeSet :: (IsSet set, Flat (Element set)) => Size set
sizeSet l acc = ofoldl' (\acc e -> size e (acc + 1)) (acc + 1) l
{-# INLINE sizeSet #-}

encodeSet :: (IsSet set, Flat (Element set)) => set -> Encoding
encodeSet = encodeList . setToList
{-# INLINE encodeSet #-}

decodeSet :: (IsSet set, Flat (Element set)) => Get set
decodeSet = setFromList <$> decodeList
{-# INLINE decodeSet #-}

{-|
Maps are saved as lists of (key,value) tuples.

>>> tst (AsMap (Data.Map.fromList ([]::[(Word8,())])))
(True,1,[0])

>>> tst (AsMap (Data.Map.fromList [(3::Word,9::Word)]))
(True,18,[129,132,128])
-}
newtype AsMap a =
  AsMap
    { unMap :: a
    } deriving (Show,Eq,Ord)

instance (IsMap map, Flat (ContainerKey map), Flat (MapValue map)) => Flat (AsMap map) where
  size   = sizeMap . unMap
  encode = encodeMap . unMap
  decode = AsMap <$> decodeMap

{-# INLINE sizeMap #-}
sizeMap :: (Flat (ContainerKey r), Flat (MapValue r), IsMap r) => Size r
sizeMap m acc =
  F.foldl' (\acc' (k, v) -> size k (size v (acc' + 1))) (acc + 1)
    . mapToList
    $ m
-- sizeMap l sz = ofoldl' (\s (k, v) -> size k (size v (s + 1))) (sz + 1) l

{-# INLINE encodeMap #-}
-- |Encode an instance of IsMap, as a list of (Key,Value) tuples
encodeMap
  :: (Flat (ContainerKey map), Flat (MapValue map), IsMap map)
  => map
  -> Encoding
encodeMap = encodeListWith (\(k, v) -> encode k <> encode v) . mapToList

{-# INLINE decodeMap #-}
-- |Decode an instance of IsMap, as a list of (Key,Value) tuples
decodeMap
  :: (Flat (ContainerKey map), Flat (MapValue map), IsMap map) => Get map
decodeMap = mapFromList <$> decodeListWith ((,) <$> decode <*> decode)

