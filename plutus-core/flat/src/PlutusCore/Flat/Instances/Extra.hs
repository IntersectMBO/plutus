{-# LANGUAGE FlexibleInstances #-}

module PlutusCore.Flat.Instances.Extra where

import PlutusCore.Flat.Class (Flat (..))
import PlutusCore.Flat.Decoder (dBool)
import PlutusCore.Flat.Encoder (eFalse, eTrue, (<>))
import PlutusCore.Flat.Instances.Base ()
import Prelude hiding ((<>))

{-$setup
>>> import PlutusCore.Flat.Instances.Test -}

{-|
For better encoding/decoding performance, it is useful to declare instances of concrete list types, such as [Char].

>>> tstBits ""
(True,1,"0")

>>> tstBits "aaa"
(True,28,"10110000 11011000 01101100 0010") -}
instance {-# OVERLAPPING #-} Flat [Char] where
  encode [] = eFalse
  encode (x : xs) = eTrue <> encode x <> encode xs
  decode = do
    tag <- dBool
    if tag then (:) <$> decode <*> decode else pure []
  size [] n = 1 + n
  size (x : xs) n = 1 + size x (size xs n)
