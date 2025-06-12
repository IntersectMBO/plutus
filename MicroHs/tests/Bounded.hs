module Bounded where

import Data.Int
import Data.Word

printBounds :: forall a. (Bounded a, Show a) => IO ()
printBounds = print (minBound @a, maxBound @a)

main :: IO ()
main = do
  printBounds @Int8
  printBounds @Int16
  printBounds @Int32
  printBounds @Word8
  printBounds @Word16
  printBounds @Word32
