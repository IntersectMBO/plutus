{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE ViewPatterns              #-}

module Flat.Instances.Util
    ( module F
    --     sizeList
    -- , decodeList
    -- , encodeList
    , encodeArray
    )
where

import Flat.Class as F
import Flat.Decoder as F
import Flat.Encoder as F
import Flat.Types as F
-- import           Data.List
-- import GHC.Exts(IsList)

-- -- $setup
-- >>> import Flat.Instances.Base()
-- >>> import Flat.Instances.Test
-- >>> let test = tstBits

-- {-|
-- >>> test []
-- (True,1,"0")

-- >>> test [1::Word8]
-- (True,10,"10000000 10")
-- -}

-- {-# INLINE sizeList #-}
-- sizeList :: Flat a => [a] -> NumBits -> NumBits
-- sizeList l sz = foldl' (\s e -> size e (s + 1)) (sz + 1) l

-- {-# INLINE encodeList #-}
-- encodeList :: Flat a => [a] -> Encoding
-- encodeList = encodeListWith encode

-- {-# INLINE decodeList #-}
-- decodeList :: Flat a => Get [a]
-- decodeList = decodeListWith decode

{-# INLINE encodeArray #-}
encodeArray :: Flat a => [a] -> Encoding
encodeArray = encodeArrayWith encode
