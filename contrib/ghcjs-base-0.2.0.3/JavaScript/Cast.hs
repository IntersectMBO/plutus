{-# LANGUAGE ScopedTypeVariables, ForeignFunctionInterface, JavaScriptFFI #-}

module JavaScript.Cast ( Cast(..)
                       , cast
                       , unsafeCast
                       ) where

import GHCJS.Prim

cast :: forall a. Cast a => JSVal -> Maybe a
cast x | js_checkCast x (instanceRef (undefined :: a)) = Just (unsafeWrap x)
       | otherwise                                     = Nothing
{-# INLINE cast #-}

unsafeCast :: Cast a => JSVal -> a
unsafeCast x = unsafeWrap x
{-# INLINE unsafeCast #-}

class Cast a where
  unsafeWrap  :: JSVal -> a
  instanceRef :: a -> JSVal

-- -----------------------------------------------------------------------------

foreign import javascript unsafe 
  "$1 instanceof $2" js_checkCast :: JSVal -> JSVal -> Bool
