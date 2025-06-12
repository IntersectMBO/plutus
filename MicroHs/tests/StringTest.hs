module StringTest(module StringTest) where
default (String)

main :: IO ()
main = do
  putStrLn $ if "abc" == "abc" then "yes" else "no"
  putStrLn $ if "abc" == "adc" then "yes" else "no"
  print (1234::Int)
  print (0::Int)
  print (- (567::Int))
  print 'x'
  print '\n'
  print False
--  putStrLn $ showUnit ()
  print [1,20,3::Int]
  print [1::Int]
  print ([] :: [Int])
  print (123::Int, 'a')
  print (Nothing :: Maybe Int)
  print (Just 890 :: Maybe Int)
  print (Left   678 :: Either Int Bool)
  print (Right True :: Either Int Bool)
  print $ length "hello"

