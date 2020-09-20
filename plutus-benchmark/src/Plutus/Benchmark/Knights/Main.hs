{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-warn-unused-imports  #-}

module Main (main) where

import           ChessSetList
import           Data.Char
import           KnightHeuristic
import           Queue
import           Sort
import           Utils

import           Control.Monad
import           System.Environment

import qualified Language.PlutusCore.Pretty as PLC
import qualified Language.PlutusTx          as Tx
import           Language.PlutusTx.Prelude  as Tx
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


main :: IO ()
main = main1
            
-- PLC version
main1 :: IO ()
main1 = do
    let code = Tx.getPlc $ $$(Tx.compile [|| length $ depthSearch 150 (root boardSize) grow isFinished ||])
    -- This takes about 8s and uses 2.9 GB
    mapM_ putStrLn $ unindent . PLC.prettyPlcClassicDebug $ code

{-
        
-- Exercise the Haskell version.  This appears to work correctly.
main2:: IO ()
main2 = getArgs >>= \ss ->
       case ss of
             [s,t,d] ->
                 let size    = read s :: Integer
                     number  = read t :: Integer
                     depth   = read d :: Integer
                 in putStrLn $ printTour 100 boardSize 0 -- depth size number
             _ -> putStrLn "\nUsage: knights <board size> <number of solutions> <maximum depth>\n"

printTour :: Integer -> Integer -> Integer -> [Char]
printTour depth size number
   = show $ ((depthSearch depth (root size) grow isFinished))  -- take number ...
     where
        pp []             = []
        pp ((x,y):xs)     = "\nKnights tour with " ++ (show x)  ++
                            " backtracking moves\n" ++ (show y) ++
                            (pp xs)
-}
