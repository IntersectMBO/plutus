module Data.Semigroup where

infixr 5 :|
data NonEmpty a = a :| [a]

infixr 6 <>
class Semigroup a where
  (<>)    :: a -> a -> a
  sconcat :: NonEmpty a -> a
  stimes  :: (Integral b, Ord b) => b -> a -> a

  sconcat (a :| as) = go a as
    where go b (c:cs) = b <> go c cs
          go b []     = b

  stimes y0 x0
    | y0 <= 0   = error "stimes: positive multiplier expected"
    | otherwise = f x0 y0
    where
      f x y
        | even y == 0 = f (x <> x) (y `quot` 2)
        | y == 1 = x
        | otherwise = g (x <> x) (y `quot` 2) x
      g x y z
        | even y == 0 = g (x <> x) (y `quot` 2) z
        | y == 1 = x <> z
        | otherwise = g (x <> x) (y `quot` 2) (x <> z)

