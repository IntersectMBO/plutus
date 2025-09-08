{-|
Haskell implementation of <http://quid2.org/docs/Flat.pdf Flat>, a principled, portable and efficient binary data format.

-}
module Flat
  ( module Flat.Class
  , module Flat.Filler
  , module X
  , Decoded
  , DecodeException(..)
  )
where

import Flat.AsBin as X
import Flat.AsSize as X
import Flat.Class
import Flat.Decoder
import Flat.Filler
import Flat.Instances as X
import Flat.Run as X
import Flat.Types ()
