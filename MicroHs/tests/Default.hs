module Default(main) where
default Num (Int, Double)
default IsString (String)
default Show (())

main :: IO ()
main = do
  print 1
  print 1.5
  print []
  print "foo"
