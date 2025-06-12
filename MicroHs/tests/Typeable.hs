module Typeable(main) where
import Data.Proxy
import Data.Typeable

data T = A
  deriving Typeable

data P a = B a
  deriving (Typeable)

main :: IO ()
main = do
  print $ typeOf True
  print $ typeOf (return True :: IO Bool)
  print $ typeOf ('a', False)
  print $ typeRep (Proxy :: Proxy Monad)
  print $ typeOf A
  print $ typeOf (B (B A))
  print $ typeOf [1::Int]
  print $ typeOf ((+) :: Int -> Int -> Int)
