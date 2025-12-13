{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Vector.Orphans () where

import Data.Hashable (Hashable (hashWithSalt))
import Data.Vector.Strict qualified as Strict
import NoThunks.Class (NoThunks (..))
import PlutusCore.Flat (Flat (..))
import PlutusCore.Flat.Instances.Vector ()

instance Hashable a => Hashable (Strict.Vector a) where
  hashWithSalt = Strict.foldl' hashWithSalt

instance NoThunks a => NoThunks (Strict.Vector a) where
  wNoThunks ctx = wNoThunks ctx . Strict.toList
  showTypeOf _proxy = "Strict.Vector"

{- The `flat` library does not provide a `Flat` instance for
`Vector.Strict.Vector`.  We could encode and decode strict vectors by converting
them to and from lazy vectors (for which there is a `Flat` instance), but
experiments show that deserialisation is actually faster by about 5-10% if we
encode vectors as lists.  This incurs a slight size penalty (lists require one
bit of overhead per entry whereas vectors can be encoded with an overhead of one
byte per 255 elements), but this is offset by the decoding speedup.  Encoding
vectors as lists also simplifies maintenance and specification. -}
instance Flat a => Flat (Strict.Vector a) where
  size = size . Strict.toList
  encode = encode . Strict.toList
  decode = Strict.fromList <$> decode
