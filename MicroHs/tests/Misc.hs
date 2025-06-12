module Misc(module Misc) where

first :: forall a b . (a, b) -> a
first ab =
  let { (a, b) = ab }
  in  a

main :: IO ()
main = do
  print $ first (10::Int,20::Int)
