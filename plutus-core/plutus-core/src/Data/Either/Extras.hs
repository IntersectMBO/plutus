module Data.Either.Extras
  ( unsafeFromEither
  , fromRightM
  ) where

import Control.Exception

-- | If argument is `Left` throw an exception, otherwise return the value inside `Right`.
unsafeFromEither :: Exception e => Either e a -> a
unsafeFromEither = either throw id
{-# INLINE unsafeFromEither #-}

{-| If argument is `Right` return its value,
otherwise apply the given action to the value of Left and return its result. -}
fromRightM :: Monad m => (a -> m b) -> Either a b -> m b
fromRightM f = either f pure
{-# INLINE fromRightM #-}
