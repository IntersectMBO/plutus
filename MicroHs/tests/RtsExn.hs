module RtsExn where
import Control.Exception

main :: IO ()
main = do
  r <- try $ print (1 `quot` 0 ::Int)
  print (r :: Either SomeException ())
