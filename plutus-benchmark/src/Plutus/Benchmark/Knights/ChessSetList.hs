{-# LANGUAGE NoImplicitPrelude #-}

module Plutus.Benchmark.Knights.ChessSetList
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

import           Language.PlutusTx.Prelude as Tx hiding (init)


type Tile     = (Integer,Integer)

data ChessSet = Board
                Integer      -- Size of board (along edge)
                Integer      -- Current move number
                (Maybe Tile) -- Initial square: see Note [deleteFirst] below
                [Tile]       -- All squares visited (in reverse: the last element is the initial square).

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

-- Remove the last element from a list
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


{-  Note [deleteFirst].
   deleteFirst removes the first position from the tour.
   Since the sequence of positions (ts) is stored in reverse this involves
   deleting the last element of ts and also storing the second-last element of
   ts as the new starting position.  In the strict world this will *fail* if the
   length of ts is 1.  The lazy version got away with this because the starting
   position is never examined in that case (possibly just through luck: with
   enough backtracking that might still happen).  To solve this we have to store
   the starting position as a Maybe value, deferring any error until we actually
   look at it.
-}

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


{-

{-# INLINABLE shint #-}
shint :: Tx.Integer -> Tx.String
shint n =
    if n == 0 then "0"
       else if n == 1 then "1"
            else if n == 2 then "2"
                 else if n == 3 then "3"
                      else if n == 4 then "4"
                           else if n == 5 then "5"
                                else if n == 6 then "6"
                                     else if n == 7 then "7"
                                          else "?"
{-# INLINABLE shl #-}
shl :: [Integer] -> String
shl []        = "0"
shl [_]       = "1"
shl [_,_]     = "2"
shl [_,_,_]   = "3"
shl [_,_,_,_] = "4"
shl _         = "?"


-- Everything below here is only needed for printing boards.
-- This is useful for debugging.

instance Show ChessSet where
   showsPrec _ (Board sze n _ ts)
      = showString (printBoard sze sortedTrail 1)
        where sortedTrail = quickSort (assignMoveNo ts sze n)

assignMoveNo :: [Tile] -> Integer -> Integer -> [Tile]
assignMoveNo [] _ _
   = []
assignMoveNo ((x,y):t) size z
   = (((y-1)*size)+x,z):assignMoveNo t size (z-1)

printBoard :: Integer -> [Tile] -> Integer -> String
printBoard s [] n
   | (n  > (s*s))   = ""
   | ((n `mod` s) /=0)= "*"++(spaces (s*s) 1) ++(printBoard s [] (n+1))
   | ((n `mod` s) ==0)= "*\n"                 ++(printBoard s [] (n+1))
printBoard s trail@((i,j):xs) n
   | (i==n) &&
     ((n `mod` s) ==0) = (show j)++"\n"++(printBoard s xs (n+1))
   | (i==n) &&
     ((n `mod` s) /=0)= (show j)++(spaces (s*s) j)++(printBoard s xs    (n+1))
   | ((n `mod` s) /=0)= "*"     ++(spaces (s*s) 1)++(printBoard s trail (n+1))
   | ((n `mod` s) ==0)= "*\n"                     ++(printBoard s trail (n+1))
printBoard _ _ _ = "?"

spaces :: Integer -> Integer -> String
spaces s y = take ((logTen s) - (logTen y) + 1) [' ',' '..]
                 where
                   logTen :: Integer -> Integer
                   logTen 0 = 0
                   logTen x = 1 + logTen (x `div` 10)


PlutusTx.makeLift ''ChessSet
-}
