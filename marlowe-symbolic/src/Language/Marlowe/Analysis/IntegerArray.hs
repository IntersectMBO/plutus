{-# LANGUAGE OverloadedLists #-}
module Language.Marlowe.Analysis.IntegerArray where

import           Data.List      (genericTake)
import           Data.SBV
import           Data.SBV.List  as SL
import           Data.SBV.Maybe as SM
import           Data.SBV.Tuple as ST
import           Prelude        hiding (all, lookup)

type NIntegerArray = [Maybe Integer]
type IntegerArray = SList (Maybe Integer)

empty :: Integer -> IntegerArray
empty n = implode $ genericTake n $ repeat sNothing

insert :: Integer -> SInteger -> IntegerArray -> IntegerArray
insert n v a = before .++ (sJust v .: after)
  where before = SL.take (literal (n - 1)) a
        after = SL.drop (literal n) a

lookup :: Integer -> IntegerArray -> SMaybe Integer
lookup n a = a .!! literal (n - 1)

member :: Integer -> IntegerArray -> SBool
member k s = SM.isJust $ lookup k s

findWithDefault :: Integer -> Integer -> IntegerArray -> SInteger
findWithDefault def k s = SM.maybe (literal def) id (lookup k s)

delete :: Integer -> IntegerArray -> IntegerArray
delete n a = before .++ (sNothing .: after)
  where before = SL.take (literal (n - 1)) a
        after = SL.drop (literal n) a

