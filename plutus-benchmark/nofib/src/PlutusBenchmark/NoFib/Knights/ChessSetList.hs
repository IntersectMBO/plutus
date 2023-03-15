{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- Turning this off makes things fail, should investigate why
{-# OPTIONS_GHC -fno-strictness #-}

module PlutusBenchmark.NoFib.Knights.ChessSetList
    ( Tile,
      ChessSet (..),
      createBoard,
      sizeBoard,
      addPiece,
      deleteFirst,
      noPieces,
      positionPiece,
      lastPiece,
      firstPiece,
      pieceAtTile,
      isSquareFree
    ) where

import Control.DeepSeq (NFData)
import GHC.Generics

import PlutusBenchmark.NoFib.Knights.Sort
import PlutusBenchmark.NoFib.Knights.Utils

import PlutusTx.Prelude as Tx

import Prelude qualified as Haskell


type Tile     = (Integer,Integer)

data ChessSet = Board
                Integer      -- % Size of board (along edge)
                Integer      -- % Current move number
                (Maybe Tile) -- % Initial square: see Note [deleteFirst] below
                [Tile]       -- % All squares visited (in reverse: the last element is the initial
                             -- square).
                deriving stock (Generic)
                deriving anyclass (NFData)
instance Tx.Eq ChessSet where
    _ == _ = True

instance Tx.Ord ChessSet where
    _ <= _ = True

{-# INLINABLE createBoard #-}
createBoard :: Integer -> Tile -> ChessSet
createBoard x t = Board x 1 (Just t) [t]

{-# INLINABLE sizeBoard #-}
sizeBoard :: ChessSet -> Integer
sizeBoard (Board s _ _ _) = s

{-# INLINABLE noPieces #-}
noPieces :: ChessSet -> Integer
noPieces (Board _ n _ _) = n

{-# INLINABLE addPiece #-}
addPiece :: Tile -> ChessSet -> ChessSet
addPiece t (Board s n f ts) = Board s (n+1) f (t:ts)

-- % Remove the last element from a list
{-# INLINABLE init #-}
init :: [a] -> [a]
init l = case reverse l of
           _:as -> reverse as
           []   -> Tx.error ()

{-# INLINABLE secondLast #-}
secondLast :: [a] -> Maybe a
secondLast l =
    case reverse l of
      []    -> Tx.error ()
      [_]   -> Nothing
      _:a:_ -> Just a


{-%  Note [deleteFirst].
    deleteFirst removes the first position from the tour.
    Since the sequence of positions (ts) is stored in reverse this involves
    deleting the last element of ts and also storing the second-last element of
    ts as the new starting position.  In the strict world this will *fail* if the
    length of ts is 1.  The lazy version got away with this because the starting
    position is never examined in that case (possibly just through luck: with
    enough backtracking that might still happen).  To solve this we have to store
    the starting position as a Maybe value, deferring any error until we actually
    look at it.
%-}

{-# INLINABLE deleteFirst #-}
deleteFirst :: ChessSet -> ChessSet
deleteFirst (Board s n _ ts) =
    Board s (n-1) f' ts'
        where ts' = init ts
              f' = secondLast ts

{-# INLINABLE positionPiece #-}
positionPiece :: Integer -> ChessSet -> Tile
positionPiece x (Board _ n _ ts) = ts Tx.!! (n - x)

{-# INLINABLE lastPiece #-}
lastPiece :: ChessSet -> Tile
lastPiece (Board _ _ _ (t:_)) = t
lastPiece _                   = Tx.error ()

{-# INLINABLE firstPiece #-}
firstPiece :: ChessSet -> Tile
firstPiece (Board _ _ f _) =
    case f of Just tile -> tile
              Nothing   -> Tx.error ()

{-# INLINABLE pieceAtTile #-}
pieceAtTile :: Tile -> ChessSet -> Integer
pieceAtTile x0 (Board _ _ _ ts)
   = findPiece x0 ts
     where
        findPiece _ [] = Tx.error ()
        findPiece x (y:xs)
           | x == y    = 1 + Tx.length xs
           | otherwise = findPiece x xs


{-# INLINABLE notIn #-}
notIn :: Eq a => a  -> [a] -> Bool
notIn _ []     = True
notIn x (a:as) = (x /= a) && (notIn x as)

{-# INLINABLE isSquareFree #-}
isSquareFree :: Tile -> ChessSet -> Bool
isSquareFree x (Board _ _ _ ts) = notIn x ts


-- % Everything below here is only needed for printing boards.
-- % This is useful for debugging.

instance Haskell.Show ChessSet where
   showsPrec _ (Board sze n _ ts)
      = Haskell.showString (printBoard sze sortedTrail 1)
        where sortedTrail = quickSort (assignMoveNo ts sze n)

assignMoveNo :: [Tile] -> Integer -> Integer -> [Tile]
assignMoveNo [] _ _
   = []
assignMoveNo ((x,y):t) size z
   = (((y-1)*size)+x,z):assignMoveNo t size (z-1)

printBoard :: Integer -> [Tile] -> Integer -> Haskell.String
printBoard s [] n
   | (n  > (s*s))   = ""
   | ((n `Haskell.mod` s) /=0)= "*"++(spaces (s*s) 1) ++(printBoard s [] (n+1))
   | ((n `Haskell.mod` s) ==0)= "*\n"                 ++(printBoard s [] (n+1))
printBoard s trail@((i,j):xs) n
   | (i==n) &&
     ((n `Haskell.mod` s) ==0) = (Haskell.show j)++"\n"++(printBoard s xs (n+1))
   | (i==n) &&
     ((n `Haskell.mod` s) /=0)= (Haskell.show j)++(spaces (s*s) j)++(printBoard s xs    (n+1))
   | ((n `Haskell.mod` s) /=0)= "*"     ++(spaces (s*s) 1)++(printBoard s trail (n+1))
   | ((n `Haskell.mod` s) ==0)= "*\n"                     ++(printBoard s trail (n+1))
printBoard _ _ _ = "?"

spaces :: Integer -> Integer -> Haskell.String
spaces s y =
    take' ((logTen s) - (logTen y) + 1) [' ',' '..]
        where
          logTen :: Integer -> Integer
          logTen 0 = 0
          logTen x = 1 + logTen (x `Haskell.div` 10)
