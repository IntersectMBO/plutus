module Integer(main) where
import System.IO.Serialize
import System.IO.StringHandle

main :: IO ()
main = do
  print $ (1000::Integer) == 1000
  print $ ((10::Integer)^(100::Int)) /= 0
  print $ show (product [1..100::Integer]) == "93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976156518286253697920827223758251185210916864000000000000000000000000"
  let i = 1234567890123456789012345678901234567890 :: Integer
  print i
  s <- handleWriteToString (\ h -> hSerialize h i)
  h <- stringToHandle s
  i' <- hDeserialize h
  print $ i == i'
