module Eq(main) where

main :: IO ()
main = do
  print [1==(1::Int), 'a'=='a', 1.1==(1.1::Double),
                   True==True, False==False,
                   (Nothing::Maybe Int)==Nothing, Just (1::Int) == Just 1,
                   [1,2,3] == [1,2,3::Int],
                   (1,2) == (1::Int,2::Int),
                   (Left 1 :: Either Int Char) == Left 1, (Right 'a' :: Either Int Char) == Right 'a'
                  ]
  print [1==(2::Int), 'a'=='b', 1.1==(1.2::Double),
                   True==False, False==True,
                   Nothing==Just (1::Int), Just (1::Int) == Nothing,
                   [1,2,3] == [1,2,4::Int],
                   (1,2) == (1::Int,4::Int),
                   Left (1::Int) == Right 'a', Right 'a' == Left (1::Int)
                  ]
