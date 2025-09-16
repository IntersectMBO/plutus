module PlutusCore.Flat.Instances.DList
  ()
where

import Data.DList (DList, fromList, toList)
import PlutusCore.Flat.Class (Flat (..))
import PlutusCore.Flat.Instances.Mono (decodeList, encodeList, sizeList)

-- $setup
-- >>> import PlutusCore.Flat.Instances.Test
-- >>> import PlutusCore.Flat.Instances.Base()
-- >>> import PlutusCore.Flat.Run
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
