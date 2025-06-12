module Block where

main :: IO ()
main = do
  let x = quot
            do 10 + 20
            do 2 * 3
  print x
