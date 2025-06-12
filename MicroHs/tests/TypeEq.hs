module TypeEq(main) where

foo :: forall a . (a ~ Bool) => a -> a
foo = not

data Exp a
  = (a ~ Int)  => Int Int
  | (a ~ Int)  => Add (Exp Int) (Exp Int)
  | (a ~ Bool) => Equ (Exp Int) (Exp Int)
  |               Iff (Exp Bool) (Exp a) (Exp a)

eval :: forall a . Exp a -> a
eval (Int i)       = i
eval (Add e1 e2)   = eval e1 + eval e2
eval (Equ e1 e2)   = eval e1 == eval e2
eval (Iff c e1 e2) = if eval c then eval e1 else eval e2

e1 :: Exp Int
e1 = Iff (Add (Int 1) (Int 2) `Equ` Int 3) (Int 1) (Int 999)

data GExp a where
  GInt :: Int -> GExp Int
  GAdd :: GExp Int -> GExp Int -> GExp Int
  GEqu :: GExp Int -> GExp Int -> GExp Bool
  GIff :: GExp Bool -> GExp a -> GExp a -> GExp a

geval :: GExp a -> a
geval (GInt i)       = i
geval (GAdd e1 e2)   = geval e1 + geval e2
geval (GEqu e1 e2)   = geval e1 == geval e2
geval (GIff c e1 e2) = if geval c then geval e1 else geval e2

ge1 :: GExp Int
ge1 = GIff (GAdd (GInt 1) (GInt 2) `GEqu` GInt 3) (GInt 1) (GInt 999)

data ParenResult a where
  ParenResult :: a -> (ParenResult a)

data Foo c a where
  Foo :: a -> Foo c a

unFoo :: Foo c a -> a
unFoo (Foo a) = a

data Bar b a where
  Bar :: Bar a a

bar :: Bar b a -> a -> b
bar c x = case c of Bar -> x

data Tree a where
  Leaf :: a -> Tree a
  Branch :: Tree a -> Tree a -> Tree a

toList :: Tree a -> [a]
toList t = go t []
  where
    go (Leaf x) xs     = x:xs
    go (Branch l r) xs = go l (go r xs)

data R a where
  Pure :: a -> R a
  Map :: (a -> b) -> R a -> R b
  Alt :: R a -> R a -> R a

instance (Show a) => Show (R a) where
  show (Pure a) = "Pure " ++ show a

splat :: R a -> [R a]
splat t = go t []
  where
    go (Alt l r) ts = go l (go r ts)
    go t ts         = t:ts

main :: IO ()
main = do
  print (foo True)
  print (eval e1)
  print (geval ge1)
  print (unFoo (Foo (2::Int)))
  print (toList (Branch (Leaf (1::Int)) (Branch (Leaf 2) (Leaf 3))))
  print (splat (Alt (Pure 'a') (Pure 'b')))
