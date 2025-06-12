module ParseInd(main) where

-- The parse error generateing a '}'

main :: IO ()
main = do
  print (foo 1)
  print (bar True)
  baz 1

foo :: Int -> Int
foo a = let x = a+1 in x

bar :: Bool -> Bool
bar x = not (case x of True -> False; False -> True)

baz :: Int -> IO ()
baz i = (do print i) >> (do print (i+1))
