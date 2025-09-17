{-# LANGUAGE FlexibleInstances #-}
module PlutusCore.Flat.Instances.Extra where

import PlutusCore.Flat.Class (Flat)
import PlutusCore.Flat.Instances.Base ()

-- $setup
-- >>> import PlutusCore.Flat.Instances.Test

{- |
For better encoding/decoding performance, it is useful to declare instances of concrete list types, such as [Char].

>>> tstBits ""
(True,1,"0")

>>> tstBits "aaa"
(True,28,"10110000 11011000 01101100 0010")
-}
instance {-# OVERLAPPING #-} Flat [Char]

