{-# LANGUAGE BangPatterns #-}

-- | The Flat class for binary serialization
module PlutusCore.Flat.Class
  ( -- * The Flat class
    Flat (..)
  , getSize
  )
where

import PlutusCore.Flat.Decoder.Types (Get)
import PlutusCore.Flat.Encoder (Encoding, NumBits)

-- | Calculate the maximum size in bits of the serialisation of the value
getSize :: Flat a => a -> NumBits
getSize a = size a 0

{-| Class of types that can be encoded/decoded

Encoding a value involves three steps:

* calculate the maximum size of the serialised value, using `size`

* preallocate a buffer of the required size

* encode the value in the buffer, using `encode` -}
class Flat a where
  -- | Return the encoding corrresponding to the value
  encode :: a -> Encoding

  -- | Decode a value
  decode :: Get a

  {-| Add maximum size in bits of the value to the total count

  Used to calculated maximum buffer size before encoding -}
  size :: a -> NumBits -> NumBits
