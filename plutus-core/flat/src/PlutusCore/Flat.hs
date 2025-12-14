{-|
Haskell implementation of <http://quid2.org/docs/Flat.pdf Flat>, a principled, portable and efficient binary data format. -}
module PlutusCore.Flat
  ( module PlutusCore.Flat.Class
  , module PlutusCore.Flat.Filler
  , module X
  , Decoded
  , DecodeException (..)
  )
where

import PlutusCore.Flat.AsBin as X
import PlutusCore.Flat.AsSize as X
import PlutusCore.Flat.Class
import PlutusCore.Flat.Decoder
import PlutusCore.Flat.Filler
import PlutusCore.Flat.Instances as X
import PlutusCore.Flat.Run as X
import PlutusCore.Flat.Types ()
