{-# LANGUAGE NoImplicitPrelude #-}

module PlutusBenchmark.NoFib.Knights.KnightHeuristic
  ( ChessSet
  , startTour
  , descendents
  , tourFinished
  ) where

import PlutusBenchmark.NoFib.Knights.ChessSetList
import PlutusBenchmark.NoFib.Knights.Sort (quickSort)

import PlutusTx.List as List
import PlutusTx.Prelude as Tx

data Direction = UL | UR | DL | DR | LU | LD | RU | RD

move :: Direction -> Tile -> Tile
move UL (x, y) = (x - 1, y - 2)
move UR (x, y) = (x + 1, y - 2)
move DL (x, y) = (x - 1, y + 2)
move DR (x, y) = (x + 1, y + 2)
move LU (x, y) = (x - 2, y - 1)
move LD (x, y) = (x - 2, y + 1)
move RU (x, y) = (x + 2, y - 1)
move RD (x, y) = (x + 2, y + 1)
{-# INLINEABLE move #-}

startTour :: Tile -> Integer -> ChessSet
startTour st size
  | (size `Tx.remainder` 2) == 0 = createBoard size st
  | otherwise {-Tx.trace "startTour" $ -} = Tx.error ()
{-# INLINEABLE startTour #-}

moveKnight :: ChessSet -> Direction -> ChessSet
moveKnight board dir =
  addPiece (move dir (lastPiece board)) board
{-# INLINEABLE moveKnight #-}

canMove :: ChessSet -> Direction -> Bool
canMove board dir =
  canMoveTo (move dir (lastPiece board)) board
{-# INLINEABLE canMove #-}

canMoveTo :: Tile -> ChessSet -> Bool
canMoveTo t@(x, y) board =
  (x Tx.>= 1)
    && (x Tx.<= sze)
    && (y Tx.>= 1)
    && (y Tx.<= sze)
    && isSquareFree t board
  where
    sze = sizeBoard board
{-# INLINEABLE canMoveTo #-}

descendents :: ChessSet -> [ChessSet]
descendents board =
  if (canJumpFirst board) && (deadEnd (addPiece (firstPiece board) board))
    then []
    else
      let l = List.length singles
       in if l == 0
            then map snd (quickSort (descAndNo board))
            else
              if l == 1
                then singles
                else [] -- Going to be dead end
  where
    singles = singleDescend board
{-# INLINEABLE descendents #-}

singleDescend :: ChessSet -> [ChessSet]
singleDescend board = [x | (y, x) <- descAndNo board, y == 1]
{-# INLINEABLE singleDescend #-}

descAndNo :: ChessSet -> [(Integer, ChessSet)]
descAndNo board =
  [(List.length (possibleMoves (deleteFirst x)), x) | x <- allDescend board]
{-# INLINEABLE descAndNo #-}

allDescend :: ChessSet -> [ChessSet]
allDescend board =
  map (moveKnight board) (possibleMoves board)
{-# INLINEABLE allDescend #-}

possibleMoves :: ChessSet -> [Direction]
possibleMoves board =
  [x | x <- [UL, UR, DL, DR, LU, LD, RU, RD], (canMove board x)]
{-# INLINEABLE possibleMoves #-}

deadEnd :: ChessSet -> Bool
deadEnd board = List.length (possibleMoves board) == 0
{-# INLINEABLE deadEnd #-}

canJumpFirst :: ChessSet -> Bool
canJumpFirst board =
  canMoveTo (firstPiece board) (deleteFirst board)
{-# INLINEABLE canJumpFirst #-}

tourFinished :: ChessSet -> Bool
tourFinished board =
  (noPieces board == (sze * sze)) && (canJumpFirst board)
  where
    sze = sizeBoard board
{-# INLINEABLE tourFinished #-}
