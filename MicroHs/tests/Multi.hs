module Multi(main) where
import Data.Char

class C a b where
  conv :: a -> b

instance C Int Bool where
  conv x = x /= 0

instance C Int Char where
  conv = chr

instance C Char Int where
  conv = ord

main :: IO ()
main = do
  print (conv (100::Int) :: Bool)
  print (conv (100::Int) :: Char)
  print (conv 'a' :: Int)
