module PatBind where

Just x = Just ()

y,z :: Int
(y,z) = (20,30)

u :: Int
(u, v) = (40, True)

main :: IO ()
main = do
  print x
  print y
  print z
  print u
  print v
