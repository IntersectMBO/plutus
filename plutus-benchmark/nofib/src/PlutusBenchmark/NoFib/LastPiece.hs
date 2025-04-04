{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}

{-% Last piece puzzle, adapted from nofib/spectral/last-piece.
    This is a solver for a jigsaw problem:
        see https://www.nicklevine.org/contest/2003/index.html.

  I've removed prettyprinting code for solutions and replaced Map.Map with an
  association list.  The original version collected the entire search tree,
  including paths which led to failure, and the PLC version quickly ran out of
  memory. This version prunes the search tree to keep only successful paths.  It
  still doesn't work on the CEK machine (I don't know about the CK machine: that
  took forever).
%-}

module PlutusBenchmark.NoFib.LastPiece where

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import Data.Char (isSpace)

import PlutusCore.Pretty qualified as PLC
import PlutusTx
import PlutusTx.Builtins as Tx
import PlutusTx.List qualified as List
import PlutusTx.Plugin ()
import PlutusTx.Prelude as PLC hiding (Semigroup (..), check)
import Prelude qualified as Haskell

-------------------------------------
--      Pieces
type Offset  = (Integer, Integer)
type Square  = (Integer, Integer)
     -- (1,1) is bottom LH corner

type PieceId = Tx.BuiltinString

type Board = [(Square, PieceId)]  -- Was Map.Map Square PieceId

data Piece = P PieceId
    [[Offset]]  -- Male in bottom LH
    [[Offset]]  -- Female in bottom LH
        -- In both cases, the list of offset is all the
        -- squares except the bottom LH one

data Solution = Soln Board
              | Choose [Solution]       -- Non-empty
              | Fail  -- Board Square
                deriving stock (Haskell.Show)

data Sex = Male | Female


sumList :: [Integer] -> Integer
sumList []    = 0
sumList (h:t) = h + sumList t
{-# INLINABLE sumList #-}

numSolutions :: Solution -> Integer
numSolutions (Soln _)   = 1
numSolutions (Choose l) = sumList . List.map numSolutions $ l
numSolutions Fail       = 0
{-# INLINABLE numSolutions #-}

sizeOfSolution :: Solution -> Integer
sizeOfSolution (Soln _)   = 1
sizeOfSolution (Choose l) = sumList . List.map sizeOfSolution $ l
sizeOfSolution Fail       = 1

flipSex :: Sex -> Sex
flipSex Male   = Female
flipSex Female = Male
{-# INLINABLE flipSex #-}

--      The main search

search :: Square -> Sex         -- Square we are up to
       -> Board                 -- Current board
       -> [Piece]               -- Remaining pieces
       -> Solution
search _ _ board []
  = Soln board     -- Finished
search (row,col) sex board ps      -- Next row
  | col == (maxCol+1) = search (row+1, 1) (flipSex sex) board ps
search square sex board ps     -- Occupied square
  | isJust (check board square) = search (next square) (flipSex sex) board ps
search square sex board ps
  = case mapMaybe (try square sex board) choices of
        [] -> Fail     -- board square
        ss -> prune ss -- discard failed paths
    where
      choices = [(pid, os, ps') |
                 (P pid ms fs, ps') <- pickOne ps,
                 let oss = case sex of
                             Male   -> ms
                             Female -> fs,
                 os <- oss]
{-# INLINABLE search #-}

-- % An attempt to cut down on the size of the result (not in the original program)
prune :: [Solution] -> Solution
prune ss =
    case List.filter nonFailure ss of
      []       -> Fail
      [Soln s] -> Soln s
      l        -> Choose l
      where nonFailure Fail = False
            nonFailure _    = True
{-# INLINABLE prune #-}

try :: Square -> Sex -> Board -> (PieceId,[Offset],[Piece]) -> Maybe Solution
try square sex board (pid,os,ps)
  = case fit board square pid os of
        Just board' -> Just (search (next square) (flipSex sex) board' ps)
        Nothing     -> Nothing
{-# INLINABLE try #-}


fit :: Board -> Square -> PieceId -> [Offset] -> Maybe Board
fit board square pid []     = Just (extend board square pid)
fit board square pid (o:os) =
    case extend_maybe board (square `add` o) pid of
      Just board' -> fit board' square pid os
      Nothing     -> Nothing
{-# INLINABLE fit #-}


--------------------------
--      Offsets and squares

add :: Square -> Offset -> Square
add (row,col) (orow, ocol) = (row + orow, col + ocol)
{-# INLINABLE add #-}

next :: Square -> Square
next (row,col) = (row,col+1)
{-# INLINABLE next #-}

maxRow,maxCol :: Integer
maxRow = 8
maxCol = 8
{-# INLINABLE maxRow #-}
{-# INLINABLE maxCol #-}


------------------------
--      Boards

emptyBoard :: Board
emptyBoard = [] -- Map.empty
{-# INLINABLE emptyBoard #-}

check :: Board -> Square -> Maybe PieceId
check board square = -- Map.lookup square board
    case board of
      []                   -> Nothing
      (square',pid):board' -> if square == square' then Just pid else check board' square
{-# INLINABLE check #-}

extend :: Board -> Square -> PieceId -> Board
extend board square pid = (square, pid): board -- Map.insert square pid board
{-# INLINABLE extend #-}

extend_maybe :: Board -> Square -> PieceId -> Maybe Board
extend_maybe board square@(row,col) pid
  | row > maxRow || col < 1 || col > maxCol
  = Nothing
  | otherwise
  = case check board square of
        Just _  -> Nothing
        Nothing -> Just (extend board square pid)
{-# INLINABLE extend_maybe #-}


--------------------------
--      Utility

pickOne :: [a] -> [(a,[a])]
pickOne = go id
  where
    go _ []     = []
    go f (x:xs) = (x, f xs) : go ((x :) . f) xs
{-# INLINABLE pickOne #-}


-----------------------------------
--      The initial setup

-- % Library functions is not inlinable
fromJust :: Maybe a -> a
fromJust Nothing  = Tx.error ()
fromJust (Just x) = x
{-# INLINABLE fromJust #-}

initialBoard :: Board
initialBoard = fromJust (fit emptyBoard (1,1) "a" [(1,0),(1,1)])
{-# INLINABLE initialBoard #-}

initialPieces :: [Piece]
initialPieces = [bPiece, cPiece, dPiece, ePiece, fPiece,
                 gPiece, hPiece, iPiece, jPiece, kPiece,
                 lPiece, mPiece, nPiece]
{-# INLINABLE initialPieces #-}

nPiece :: Piece
nPiece = P "n" [ [(0,1),(1,1),(2,1),(2,2)],
                 [(1,0),(1,-1),(1,-2),(2,-2)] ]
               []
{-# INLINABLE nPiece #-}

mPiece :: Piece
mPiece = P "m" [ [(0,1),(1,0),(2,0),(3,0)] ]
               [ [(0,1),(0,2),(0,3),(1,3)],
                 [(1,0),(2,0),(3,0),(3,-1)] ]
{-# INLINABLE mPiece #-}

lPiece :: Piece
lPiece = P "l" [ [(0,1),(0,2),(0,3),(1,2)],
                 [(1,0),(2,0),(3,0),(2,-1)] ]
               [ [(1,-1),(1,0),(1,1),(1,2)],
                 [(1,0),(2,0),(3,0),(1,1)] ]
{-# INLINABLE lPiece #-}

kPiece :: Piece
kPiece = P "k" [ [(0,1),(1,0),(2,0),(2,-1)] ]
               [ [(1,0),(1,1),(1,2),(2,2)] ]
{-# INLINABLE kPiece #-}


jPiece :: Piece
jPiece = P "j" [ [(0,1),(0,2),(0,3),(1,1)],
                 [(1,0),(2,0),(3,0),(1,-1)],
                 [(1,-2),(1,-1),(1,0),(1,1)] ]
               [ [(1,0),(2,0),(3,0),(2,2)] ]
{-# INLINABLE jPiece #-}

iPiece :: Piece
iPiece = P "i" [ [(1,0),(2,0),(2,1),(3,1)],
                 [(0,1),(0,2),(1,0),(1,-1)],
                 [(1,0),(1,1),(2,1),(3,1)] ]
               [ [(0,1),(1,0),(1,-1),(1,-2)] ]
{-# INLINABLE iPiece #-}

hPiece :: Piece
hPiece = P "h" [ [(0,1),(1,1),(1,2),(2,2)],
                 [(1,0),(1,-1),(2,-1),(2,-2)],
                 [(1,0),(1,1),(2,1),(2,2)] ]
               [ [(0,1),(1,0),(1,-1),(2,-1)] ]
{-# INLINABLE hPiece #-}


gPiece :: Piece
gPiece = P "g" [ ]
               [ [(0,1),(1,1),(1,2),(1,3)],
                 [(1,0),(1,-1),(2,-1),(3,-1)],
                 [(0,1),(0,2),(1,2),(1,3)],
                 [(1,0),(2,0),(2,-1),(3,-1)] ]
{-# INLINABLE gPiece #-}

fPiece :: Piece
fPiece = P "f" [ [(0,1),(1,1),(2,1),(3,1)],
                 [(1,0),(1,-1),(1,-2),(1,-3)],
                 [(1,0),(2,0),(3,0),(3,1)] ]
               [ [(0,1),(0,2),(0,3),(1,0)] ]
{-# INLINABLE fPiece #-}


ePiece :: Piece
ePiece = P "e" [ [(0,1),(1,1),(1,2)],
                 [(1,0),(1,-1),(2,-1)] ]
               [ [(0,1),(1,1),(1,2)],
                 [(1,0),(1,-1),(2,-1)] ]
{-# INLINABLE ePiece #-}

dPiece :: Piece
dPiece = P "d" [ [(0,1),(1,1),(2,1)],
                 [(1,0),(1,-1),(1,-2)] ]
               [ [(1,0),(2,0),(2,1)] ]
{-# INLINABLE dPiece #-}


cPiece :: Piece
cPiece = P "c" [ ]
               [ [(0,1),(0,2),(1,1)],
                 [(1,0),(1,-1),(2,0)],
                 [(1,-1),(1,0),(1,1)],
                 [(1,0),(1,1),(2,0)] ]
{-# INLINABLE cPiece #-}

bPiece :: Piece
bPiece = P "b"  [ [(0,1),(0,2),(1,2)],
                  [(1,0),(2,0),(2,-1)],
                  [(0,1),(1,0),(2,0)] ]
                [ [(1,0),(1,1),(1,2)] ]
{-# INLINABLE bPiece #-}

unindent :: PLC.Doc ann -> [Haskell.String]
unindent d = List.map (Haskell.dropWhile isSpace) (Haskell.lines . Haskell.show $ d)

runLastPiece :: Solution
runLastPiece = search (1,2) Female initialBoard initialPieces

mkLastPieceTerm :: Term
mkLastPieceTerm =
    compiledCodeToTerm $ $$(compile [|| runLastPiece ||])

-- -- Number of correct solutions: 3
-- -- Number including failures: 59491
