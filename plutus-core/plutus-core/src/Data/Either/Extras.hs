module Data.Either.Extras
  ( unsafeFromEither
  , fromRightM
  ) where

import Control.Exception

{-# INLINE unsafeFromEither #-}
unsafeFromEither :: Exception e => Either e a -> a
unsafeFromEither = either throw id

{-# INLINE fromRightM #-}
fromRightM :: Monad m => (a -> m b) -> Either a b -> m b
fromRightM f = either f pure
