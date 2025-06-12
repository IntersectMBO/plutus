module Symbol(main) where

newtype T (s::Symbol) = A Int

class C a where
  m :: a -> Int

instance C (T "id") where
  m (A i) = i
instance C (T "neg") where
  m (A i) = - i
instance C (T "inc") where
  m (A i) = succ i

a :: T "id"
a = A 10
b :: T "neg"
b = A 10
c :: T "inc"
c = A 10

main :: IO ()
main = do
  print (m a)
  print (m b)
  print (m c)
  return ()
