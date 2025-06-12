-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module MicroHs.List where
import Data.List
import MHSPrelude
import Prelude qualified ()

-- Various useful list functions.
-- These are not really MicroHs specific.

------- List --------

elemBy :: (a -> a -> Bool) -> a -> [a] -> Bool
elemBy eq a = any (eq a)

-- A simple merge sort for now.
sortLE :: forall a . (a -> a -> Bool) -> [a] -> [a]
sortLE le = mergeAll . splatter
  where
    splatter [] = []
    splatter [a] = [[a]]
    splatter (a1 : a2 : as)
      | a1 `le` a2 = [a1, a2] : splatter as
      | otherwise  = [a2, a1] : splatter as

    mergeAll []   = []
    mergeAll [xs] = xs
    mergeAll xss  = mergeAll (mergePairs xss)

    mergePairs []                = []
    mergePairs [xs]              = [xs]
    mergePairs (xs1 : xs2 : xss) = merge xs1 xs2 : mergePairs xss

    merge [] ys = ys
    merge xs [] = xs
    merge axs@(x : xs) ays@(y : ys)
      | x `le` y  = x : merge xs ays
      | otherwise = y : merge axs ys


showListS :: (a -> String) -> [a] -> String
showListS sa arg =
  let
    showRest as =
      case as of
        []     -> "]"
        x : xs -> "," ++ sa x ++ showRest xs
  in
    case arg of
      []     -> "[]"
      a : as -> "[" ++ sa a ++ showRest as

anySame :: (Ord a) => [a] -> Bool
anySame = anySameByLE (<=)

anySameByLE :: (a -> a -> Bool) -> [a] -> Bool
anySameByLE le = anySameAdj . sortLE le
  where
    anySameAdj (x1 : xs@(x2 : _))
      | x2 `le` x1 = True
      | otherwise = anySameAdj xs
    anySameAdj _ = False

groupSort :: (Ord a) => [a] -> [[a]]
groupSort = group . sortLE (<=)

deleteAllBy :: forall a . (a -> a -> Bool) -> a -> [a] -> [a]
deleteAllBy _ _ []      = []
deleteAllBy eq x (y:ys) = if eq x y then deleteAllBy eq x ys else y : deleteAllBy eq x ys

deleteAllsBy :: forall a . (a -> a -> Bool) -> [a] -> [a] -> [a]
deleteAllsBy eq = foldl (flip (deleteAllBy eq))

padLeft :: Int -> String -> String
padLeft n s = replicate (n - length s) ' ' ++ s

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM _ [] = return ([], [])
partitionM p (x:xs) = do
  b <- p x
  (ts,fs) <- partitionM p xs
  return $ if b then (x:ts, fs) else (ts, x:fs)

substString :: forall a . Eq a => [a] -> [a] -> [a] -> [a]
substString _ _ [] = []
substString from to xs@(c:cs) =
  case stripPrefix from xs of
    Just rs -> to ++ substString from to rs
    _       -> c : substString from to cs

showPairS :: forall a b . (a -> String) -> (b -> String) -> (a, b) -> String
showPairS sa sb (a, b) = "(" ++ sa a ++ "," ++ sb b ++ ")"

findCommonPrefix :: Eq a => [[a]] -> [a]
findCommonPrefix [] = []
findCommonPrefix ([] : _) = []
findCommonPrefix ((x:xs) : ys) =
  let f a (b:bs) | a == b = Just bs
      f _ _ = Nothing
  in  case mapM (f x) ys of
        Just ys' -> x : findCommonPrefix (xs:ys')
        _        -> []

dropEnd :: Int -> [a] -> [a]
dropEnd n = reverse . drop n . reverse

takeEnd :: Int -> [a] -> [a]
takeEnd n = reverse . take n . reverse
