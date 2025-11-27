{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- | Instances for the containers library
module PlutusCore.Flat.Instances.Containers
  ( sizeMap
  , encodeMap
  , decodeMap
  ) where

import Data.IntMap
import Data.Map
import Data.Sequence
import Data.Set
import Data.Tree
import PlutusCore.Flat.Instances.Base ()
import PlutusCore.Flat.Instances.Mono
import PlutusCore.Flat.Instances.Util

{-$setup
>>> import PlutusCore.Flat.Instances.Test
>>> import Data.Set
>>> import Data.Sequence
>>> import Data.IntMap
>>> import Data.Map
>>> import Data.Tree
>>> import PlutusCore.Flat.Instances.Mono -}

{-|
Maps are defined as a list of (Key,Value) tuples:

@
Map = List (Key,Value)

List a = Nil | Cons a (List a)
@ -}
{-|
>>> tst (Data.IntMap.empty :: IntMap ())
(True,1,[0])

>>> asList Data.IntMap.fromList [(1,"a"),(2,"b")]
True -}
instance Flat a => Flat (IntMap a) where
  size = sizeMap
  encode = encodeMap
  decode = decodeMap

{-|
Maps are encoded as lists:

>>> tst (Data.Map.empty :: Map () ())
(True,1,[0])

>>>  asList Data.Map.fromList [("a","aa"),("b","bb")]
True

Key/Values are encoded in order:

>>> let l = [("a","aa"),("b","bb")] in tst (Data.Map.fromList l) == tst (Data.Map.fromList $ Prelude.reverse l)
True

IntMap and Map are encoded in the same way:

>>> let l = [(2::Int,"b"),(1,"a")] in tst (Data.IntMap.fromList l) == tst (Data.Map.fromList l)
True -}
instance (Flat a, Flat b, Ord a) => Flat (Map a b) where
  size = sizeMap
  encode = encodeMap
  decode = decodeMap

{-|
Data.Sequence.Seq is encoded as a list.

>>> asList Data.Sequence.fromList [3::Word8,4,7]
True

In flat <0.4, it was encoded as an Array.

If you want to restore the previous behaviour, use AsArray:

>>> tst $ AsArray (Data.Sequence.fromList [11::Word8,22,33])
(True,40,[3,11,22,33,0])

>>> tst $ Data.Sequence.fromList [11::Word8,22,33]
(True,28,[133,197,164,32]) -}
instance Flat a => Flat (Seq a) where
  size = sizeList -- . toList
  encode = encodeList -- . Data.Sequence.toList
  decode = Data.Sequence.fromList <$> decodeList

{-|
Data.Set is encoded as a list

>>> asList Data.Set.fromList [3::Word8,4,7]
True -}
instance (Flat a, Ord a) => Flat (Set a) where
  size = sizeSet
  encode = encodeSet
  decode = decodeSet

{-|
>>>  tst (Node (1::Word8) [Node 2 [Node 3 []], Node 4 []])
(True,39,[1,129,64,200,32]) -}
#if ! MIN_VERSION_containers(0,5,8)
deriving instance Generic (Tree a)
#endif

instance Flat a => Flat (Tree a)
