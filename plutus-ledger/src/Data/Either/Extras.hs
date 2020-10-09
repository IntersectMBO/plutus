module Data.Either.Extras
  ( unsafeFromEither
  ) where

unsafeFromEither :: Either String a -> a
unsafeFromEither (Left err)    = error err
unsafeFromEither (Right value) = value
