module PatSyn where
import PatSynE

f1 :: [a] -> (a, [a])
f1 (Sings a as) = (a, as)

f2 :: [a] -> a
f2 (Sing a) = a

pattern Dup :: Eq a => a -> [a]
pattern Dup a <- (dup -> (Just a))
  where Dup a = [a, a]

dup :: (Eq a) => [a] -> Maybe a
dup [x,x'] | x==x' = Just x
dup _ = Nothing

f3 :: [Int] -> Int
f3 (Dup x) = x
f3 _ = 0

f4 :: Int -> Int
f4 One = 99
f4 _ = 88

data S b = forall a . Show a => S (a,b)

instance Show b => Show (S b) where
  show (S xy) = show xy

pattern SP :: () => Show a => a -> S Bool
pattern SP a = S (a, True)

f5 :: S Bool -> String
f5 (SP x) = show x

ss :: S Bool
ss = S ((), True)

----

data T a = forall b . Show b => MkT a b

pattern ExNumPat1 :: (Num a, Eq a) => (Show b) => b -> T a
pattern ExNumPat1 x = MkT 42 x

pattern ExNumPat2 x = MkT 42 x

ft1 :: (Eq a, Num a) => T a -> String
ft1 (ExNumPat1 x) = show x

ft2 :: (Eq a, Num a) => T a -> String
ft2 (ExNumPat2 x) = show x


main :: IO ()
main = do
  print $ Sing 1
  print $ Swap 1 2
  print $ f1 [3]
  print $ f2 [4]
--  print (Sings 1 [2])  this is an error, of course
  print (Dup 22)
  print $ f3 [11,11]
  print $ f3 [11,12]
  print (One :: Int)
  print (One :: Double)
  print $ f4 1
  print $ f4 2
  print $ SP ()
  print $ f5 ss

  let x = MkT 42 True
      y = ExNumPat1 ()
      z = ExNumPat2 ()
  print (ft1 x, ft2 x)
  print (ft1 y, ft2 y)
  print (ft1 z, ft2 z)
  print AA
  case A of AA -> print 42
