module RecMdlA where
import {-# SOURCE #-} RecMdl

data A = A1 | A2 B
  deriving (Show)

g :: Int -> Int
g x = h x * 2
