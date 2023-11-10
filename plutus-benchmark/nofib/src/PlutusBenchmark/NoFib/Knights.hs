{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusBenchmark.NoFib.Knights where

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import Data.Char
import PlutusBenchmark.NoFib.Knights.ChessSetList
import PlutusBenchmark.NoFib.Knights.KnightHeuristic
import PlutusBenchmark.NoFib.Knights.Queue

import PlutusCore.Pretty qualified as PLC
import PlutusTx qualified as Tx
import PlutusTx.Prelude as Tx
import Prelude qualified as Haskell

{-# INLINABLE zipConst #-}
zipConst :: a -> [b] -> [(a,b)]
zipConst a = map ((,) a)

{-# INLINABLE grow #-}
grow :: (Integer,ChessSet) -> [(Integer,ChessSet)]
grow (x,y) = zipConst (x+1) (descendents y)

{-# INLINABLE isFinished #-}
isFinished :: (Integer,ChessSet) -> Bool
isFinished (_,y) = tourFinished y

{-# INLINABLE interval #-}
interval :: Integer -> Integer -> [Integer]
interval a0 b = go a0 where
    go a = if a > b then [] else a : go (a + 1)

-- % Original version used infinite lists.
{-# INLINABLE mkStarts #-}
mkStarts :: Integer -> [(Integer, ChessSet)]
mkStarts sze =
    let l = [startTour (x,y) sze | x <- interval 1 sze, y <- interval 1 sze]
        numStarts = Tx.length l  -- = sze*sze
    in Tx.zip (replicate numStarts (1-numStarts)) l

{-# INLINABLE root #-}
root :: Integer -> Queue (Integer, ChessSet)
root sze = addAllFront (mkStarts sze) createQueue

{-% Original version
root sze = addAllFront
             (Tx.zip [-(sze*sze)+1,-(sze*sze)+1..]
                  (zipWith
                     startTour
                      [(x,y) | x <- [1..sze], y <- [1..sze]]
                     (take' (sze*sze) [sze,sze..])))
             createQueue
%-}

type Solution = (Integer, ChessSet)

{-# INLINABLE depthSearch #-}
-- % Added a depth parameter to stop things getting out of hand in the strict world.
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

-- % Only for textual output of PLC scripts
unindent :: PLC.Doc ann -> [Haskell.String]
unindent d = map (Haskell.dropWhile isSpace) $ (Haskell.lines . Haskell.show $ d)


-- % Haskell entry point for testing
{-# INLINABLE runKnights #-}
runKnights :: Integer -> Integer -> [Solution]
runKnights depth boardSize = depthSearch depth (root boardSize) grow isFinished

mkKnightsCode :: Integer -> Integer -> Tx.CompiledCode [Solution]
mkKnightsCode depth boardSize =
       $$(Tx.compile [|| runKnights ||])
             `Tx.unsafeApplyCode` Tx.liftCodeDef depth
                  `Tx.unsafeApplyCode` Tx.liftCodeDef boardSize

mkKnightsTerm :: Integer -> Integer -> Term
mkKnightsTerm depth boardSize = compiledCodeToTerm $ mkKnightsCode depth boardSize

Tx.makeLift ''ChessSet
