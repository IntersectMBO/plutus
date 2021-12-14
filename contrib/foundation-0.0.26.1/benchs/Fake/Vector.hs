module Fake.Vector
    ( Vector
    , fromList
    , toList
    , length
    , splitAt
    , take
    , takeWhile
    , break
    , reverse
    , filter
    , foldl'
    , foldl1'
    , foldr
    , and
    , all
    , any
    , concat
    ) where

import Prelude (undefined)

data Vector ty = Vector

fromList _  = Vector
toList :: Vector ty -> [ty]
toList _ = undefined
length      = undefined
splitAt _ _ = (undefined, undefined)
take        = undefined
break   _ _ = (undefined, undefined)
takeWhile _ _ = undefined
reverse     = undefined
filter _    = undefined
foldl' :: (ty -> a -> a) -> a -> Vector ty -> a
foldl' _ _ _ = undefined
foldl1' :: (ty -> ty -> ty) -> Vector ty -> a
foldl1' _ _ = undefined
foldr :: (a -> ty -> a) -> a -> Vector ty -> a
foldr _ _ _ = undefined
and _ _ = undefined
all _ _ = undefined
any _ _ = undefined
concat = undefined
