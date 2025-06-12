module MutRec(main) where

main :: IO ()
main = do
  let even i = i == 0 || odd  (i - 1)
      odd  i = i /= 0 && even (i - 1)
  print $ map even [1::Int .. 5] ++ map odd [1 .. 5]
