-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module MicroHs.IntMap(
  IntMap,
  empty, lookup, insert, fromList, toList, insertWith, (!), keys
  ) where
import MHSPrelude hiding (lookup)
import Prelude qualified ()

data IntMap a
  = Empty
  | Leaf Int a
  | Node (IntMap a) (IntMap a) (IntMap a) (IntMap a)
  --Xderiving (Show)

{-
-- This works for y>0
divModX :: Int -> Int -> (Int, Int)
divModX x y =
  let
    q = quot x y
    r = rem x y
  in
    if x >= 0 || r == 0 then
      (q, r)
    else
      (q - 1, r + y)
-}

div4 :: Int -> Int
div4 i = {-if i < 0 then error "div4" else-} i `quot` 4
mod4 :: Int -> Int
mod4 i = {-if i < 0 then error "mod4" else-} i `rem` 4

empty :: forall a . IntMap a
empty = Empty

lookup :: forall a . Int -> IntMap a -> Maybe a
lookup k am =
  case am of
    Empty -> Nothing
    Leaf i a -> if k == i then Just a else Nothing
    Node m0 m1 m2 m3 ->
      let
        d = div4 k
        m = mod4 k
      in      if 0 == m then lookup d m0
         else if 1 == m then lookup d m1
         else if 2 == m then lookup d m2
         else                lookup d m3

insert :: forall a . Int -> a -> IntMap a -> IntMap a
insert = insertWith const

fromList :: forall a . [(Int, a)] -> IntMap a
fromList = foldr (uncurry insert) empty

-- XXX There must be a better way
toList :: forall a . IntMap a -> [(Int, a)]
toList am =
  let
    f o (k, a) = (k*4 + o, a)
  in
    case am of
      Empty -> []
      Leaf l a -> [(l, a)]
      Node m0 m1 m2 m3 ->
        map (f 0) (toList m0) `merge`
        map (f 1) (toList m1) `merge`
        map (f 2) (toList m2) `merge`
        map (f 3) (toList m3)

merge :: forall a . [(Int, a)] -> [(Int, a)] -> [(Int, a)]
merge [] ys                               = ys
merge xs []                               = xs
merge xxs@(xa@(x,_):xs) yys@(yb@(y,_):ys) = if x < y then xa : merge xs yys else yb : merge xxs ys

keys :: forall a . IntMap a -> [Int]
keys = map fst . toList

(!) :: forall a . IntMap a -> Int -> a
(!) m k =
  case lookup k m of
    Just i  -> i
    Nothing -> error "Data.IntMap.!"

insertWith :: forall a . (a -> a -> a) -> Int -> a -> IntMap a -> IntMap a
insertWith comb ak a =
  let
    ins k am =
      case am of
        Empty -> Leaf k a
        Leaf i b ->
          if k == i then
            Leaf k (comb a b)
          else
            ins k $ single i b
        Node m0 m1 m2 m3 ->
          let
            d = div4 k
            m = mod4 k
          in      if 0 == m then Node (ins d m0) m1 m2 m3
             else if 1 == m then Node m0 (ins d m1) m2 m3
             else if 2 == m then Node m0 m1 (ins d m2) m3
             else                Node m0 m1 m2 (ins d m3)
  in ins ak

single :: Int -> a -> IntMap a
single k a = --insert k a $ Node Empty Empty Empty Empty
  let
    m = mod4 k
    d = div4 k
    l = Leaf d a
  in      if 0 == m then Node l     Empty Empty Empty
     else if 1 == m then Node Empty l     Empty Empty
     else if 2 == m then Node Empty Empty l     Empty
     else                Node Empty Empty Empty l
