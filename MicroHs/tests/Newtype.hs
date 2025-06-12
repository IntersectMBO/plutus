module Newtype(main) where

newtype N = N Int
newtype M a = M a

f :: N -> Int
f (N x) = x

g :: M (Int, Int) -> M Int
g (M (x, y)) = M x

showM :: forall a . (a -> String) -> M a -> String
showM sh (M x) = "(M " ++ sh x ++ ")"

main :: IO ()
main = do
  print [f (N 1), f (N 2)]
  putStrLn $ showM show (g (M (3,4)))
