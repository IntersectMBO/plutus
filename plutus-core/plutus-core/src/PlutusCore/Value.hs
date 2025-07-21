{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}

module PlutusCore.Value (
    Value,
    fromList,
) where

import Data.ByteString (ByteString)
import Data.Hashable (Hashable (..))

import PlutusPrelude

-- TODO: implement the Value type
data Value

fromList :: [(ByteString, [(ByteString, Integer)])] -> Value
fromList = undefined

-- TODO: implement/derive Eq instance
instance Eq Value where
    (==) _ _ = undefined

-- TODO: implement pretty instances
instance Pretty Value where
    pretty _ = undefined
instance PrettyBy config Value where
    prettyBy _ _ = undefined

-- TODO: implement (or derive) hashable instance
instance Hashable Value where
    hashWithSalt _ _ = undefined

-- TODO: implement/derive Show instance
instance Show Value where
    show _ = undefined
