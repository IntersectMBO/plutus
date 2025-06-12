-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module MicroHs.IntSet(
  IntSet,
  empty, member, insert, fromList, toList
  ) where
import MHSPrelude
import MicroHs.IntMap qualified as M
import Prelude qualified ()

newtype IntSet = I (M.IntMap ())

empty :: IntSet
empty = I M.empty

member :: Int -> IntSet -> Bool
member k (I m) =
  case M.lookup k m of
    Nothing -> False
    Just _  -> True

insert :: Int -> IntSet -> IntSet
insert k (I m) = I (M.insert k () m)

fromList :: [Int] -> IntSet
fromList is = I $ M.fromList (map (\ x -> (x, ())) is)

toList :: IntSet -> [Int]
toList (I m) = map fst (M.toList m)
