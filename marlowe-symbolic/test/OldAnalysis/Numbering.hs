module OldAnalysis.Numbering (Numbering, emptyNumbering, getNumbering, getLabel, numberOfLabels) where

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

data Numbering a = Numbering { numbering     :: Map a Integer
                             , label         :: Map Integer a
                             , lastNumbering :: Integer }
  deriving (Eq,Ord,Show,Read)

emptyNumbering :: Ord a => Numbering a
emptyNumbering = Numbering { numbering = Map.empty
                           , label = Map.empty
                           , lastNumbering = 0 }

getNewNumbering :: Ord a => Numbering a -> (Integer, Numbering a)
getNewNumbering num@Numbering {lastNumbering = x} = (nx, num{lastNumbering = nx})
  where nx = x + 1

getNumbering :: Ord a => a -> Numbering a -> (Integer, Numbering a)
getNumbering x num =
  case Map.lookup x (numbering num) of
    Just y -> (y, num)
    Nothing -> let (y, newNum) = getNewNumbering num in
               (y, newNum { numbering = Map.insert x y (numbering newNum)
                          , label = Map.insert y x (label newNum) })

getLabel :: Ord a => Integer -> Numbering a -> a
getLabel x num =
  case Map.lookup x (label num) of
    Just y  -> y
    Nothing -> error "Numbering not defined"

numberOfLabels :: Ord a => Numbering a -> Integer
numberOfLabels = lastNumbering

