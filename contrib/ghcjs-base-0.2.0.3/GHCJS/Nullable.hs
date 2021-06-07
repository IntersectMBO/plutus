module GHCJS.Nullable ( Nullable(..)
                      , nullableToMaybe
                      , maybeToNullable
                      ) where

import GHCJS.Prim (JSVal(..))
import GHCJS.Marshal.Pure (PToJSVal(..), PFromJSVal(..))

newtype Nullable a = Nullable JSVal

nullableToMaybe :: PFromJSVal a => Nullable a -> Maybe a
nullableToMaybe (Nullable r) = pFromJSVal r
{-# INLINE nullableToMaybe #-}

maybeToNullable :: PToJSVal a => Maybe a -> Nullable a
maybeToNullable = Nullable . pToJSVal
{-# INLINE maybeToNullable #-}


