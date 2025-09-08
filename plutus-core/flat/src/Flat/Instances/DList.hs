module Flat.Instances.DList
  ()
where

import Data.DList (DList, fromList, toList)
import Flat.Class (Flat (..))
import Flat.Instances.Mono (decodeList, encodeList, sizeList)

-- $setup
-- >>> import Flat.Instances.Test
-- >>> import Flat.Instances.Base()
-- >>> import Flat.Run
-- >>> import Data.DList
-- >>> let test = tstBits

{-|
>>> test (Data.DList.fromList [7::Word,7])
(True,19,"10000011 11000001 110")

>>> let l = [7::Word,7] in flat (Data.DList.fromList l) == flat l
True
-}

instance Flat a => Flat (DList a) where
  size   = sizeList . toList
  encode = encodeList . toList
  decode = fromList <$> decodeList
