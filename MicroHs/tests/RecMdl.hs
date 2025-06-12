module RecMdl where
import RecMdlA

data B = B1 | B2 A
  deriving (Show)

h :: Int -> Int
h x = x + 100

f :: Int -> Int
f x = g (x+1)

main :: IO ()
main = do
  print (f 10)
  print (B2 (A2 B1))
