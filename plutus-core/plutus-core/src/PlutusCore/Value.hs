{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}

module PlutusCore.Value (
    Value,
    fromList,
) where

import Data.ByteString (ByteString)
import Data.Hashable (Hashable (..))
import Data.Map.Strict (Map)

import PlutusPrelude

-- TODO: implement the Value type
data Value

newtype ProtoValue =
    ProtoValue
        (Map ByteString (Map ByteString Integer))
--                        ^ non-empty     ^ non-zero

-- Value is a partially ordered monoid
-- Value as a monoid (Value, union):
--    - assoc: v1 union (v2 union v3) = (v1 union v2) union v3
--    - neutral elem: v union mempty = mempty union v = v
--    - op is well-defined: v1 union v2 is still a Value
--
--    - union is defined as map union:
--      - if conflicting keys are present in outer, the inner maps are unioned
--      - if conflicting keys are present in inner, the integers are added
--      - if the integer becomes zero, the key is removed
--      - if the inner map becomes empty, the outer key is removed
--    - so mempty is the empty map
-- order is <= (inverse of "contains"), we can call it inclusion like for sets
--  - mempty <= v (basically v contains mempty) but according to the CIP, this is false??
--  - but not all values are comparable! so the type of contains cannot be Value -> Value -> Bool
--  - the order defined in the spec is different
-- why not Map (ByteString, ByteString) Integer? like in the spec?

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
