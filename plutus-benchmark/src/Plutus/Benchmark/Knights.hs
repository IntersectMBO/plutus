{-# LANGUAGE NoImplicitPrelude #-}

module Plutus.Benchmark.Knights where

import           Data.Char
import           Plutus.Benchmark.Knights.ChessSetList
import           Plutus.Benchmark.Knights.KnightHeuristic
import           Plutus.Benchmark.Knights.Queue
import           Plutus.Benchmark.Knights.Sort
import           Plutus.Benchmark.Knights.Utils

import           Control.Monad
import           System.Environment

import           Language.PlutusCore                      (Name (..))
import qualified Language.PlutusCore.Pretty               as PLC
import           Language.PlutusCore.Universe
import qualified Language.PlutusTx                        as Tx
import           Language.PlutusTx.Prelude                as Tx
import           Language.UntypedPlutusCore

{-# INLINABLE zipConst #-}
zipConst :: a -> [b] -> [(a,b)]
zipConst _ []     = []
zipConst a (b:bs) = (a,b) : zipConst a bs

{-# INLINABLE grow #-}
grow :: (Integer,ChessSet) -> [(Integer,ChessSet)]
grow (x,y) = zipConst (x+1) (descendents y)

{-# INLINABLE isFinished #-}
isFinished :: (Integer,ChessSet) -> Bool
isFinished (_,y) = tourFinished y

{-# INLINABLE interval #-}
interval :: Integer -> Integer -> [Integer]
interval a b =
    if a > b then []
    else a:(interval (a+1) b)


{-# INLINABLE repl #-}
repl :: Integer -> Integer -> [Integer]
repl n a =
    if n == 0 then []
    else a:(repl (n-1) a)

-- Original version used infinite lists.
{-# INLINABLE mkStarts #-}
mkStarts :: Integer -> [(Integer, ChessSet)]
mkStarts sze =
    let l = [startTour (x,y) sze | x <- interval 1 sze, y <- interval 1 sze]
        numStarts = Tx.length l  -- = sze*sze
    in Tx.zip (repl numStarts (1-numStarts)) l

{-# INLINABLE root #-}
root :: Integer -> Queue (Integer, ChessSet)
root sze = addAllFront (mkStarts sze) createQueue

{- Original version
root sze = addAllFront
             (Tx.zip [-(sze*sze)+1,-(sze*sze)+1..]
                  (zipWith
                     startTour
                      [(x,y) | x <- [1..sze], y <- [1..sze]]
                     (take' (sze*sze) [sze,sze..])))
             createQueue
-}


type P = (Integer, ChessSet)

{-# INLINABLE depthSearch #-}
-- Added a depth parameter to stop things getting out of hand in the strict world.
depthSearch :: (Eq a) => Integer -> Queue a -> (a -> [a]) -> (a -> Bool) -> Queue a
depthSearch depth q growFn finFn
   | depth == 0             = []
   | emptyQueue q           = []
   | finFn (inquireFront q) = (inquireFront q):
                              (depthSearch (depth-1) (removeFront q) growFn finFn)
   | otherwise              = depthSearch (depth-1)
                                 (addAllFront (growFn (inquireFront q))
                                              (removeFront q))
                                 growFn
                                 finFn

-- Only for textual output of PLC scripts
unindent :: PLC.Doc ann -> [String]
unindent d = map (dropWhile isSpace) $ (lines . show $ d)

testlist :: [Integer]
testlist = [a+b | a <- [1,2,3,4,5], b <- [11,22,33,44,55]]

{-# INLINABLE boardSize #-}
boardSize :: Integer
boardSize = 8

{-# INLINABLE mkKnightsTerm #-}
mkKnightsTerm :: Integer -> Integer -> Term Name DefaultUni ()
mkKnightsTerm depth boardSize =
  let (Program _ _ code) = Tx.getPlc $ $$(Tx.compile [||
        \depth' boardSize' ->
            length $ depthSearch depth' (root boardSize') grow isFinished ||])
        `Tx.applyCode` Tx.liftCode depth
        `Tx.applyCode` Tx.liftCode boardSize
  in code
