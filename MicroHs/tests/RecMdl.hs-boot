module RecMdl where
import {-# SOURCE #-} RecMdlA

data B = B1 | B2 A
instance Show B

h :: Int -> Int
