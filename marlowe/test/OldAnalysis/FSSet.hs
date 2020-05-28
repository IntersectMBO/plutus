{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -w #-}
module OldAnalysis.FSSet where

import           Data.SBV
import           Data.SBV.List as SL

type NSet a = [a]
type FSSet a = SList a

empty :: Ord a => SymVal a => FSSet a
empty = []

insert :: Ord a => SymVal a => Integer -> SBV a -> FSSet a -> FSSet a
insert b v s
  | b < 0 = s
  | otherwise = ite (SL.null s)
                    (SL.singleton v)
                    (ite (v .< h)
                         (v .: s)
                         (ite (v .> h)
                              (h .: insert (b - 1) v t)
                              s))
  where h = SL.head s
        t = SL.tail s

elem :: Ord a => SymVal a => Integer -> SBV a -> FSSet a -> SBool
elem b v s
  | b < 0 = sFalse
  | otherwise = ite (SL.null s)
                    sFalse
                    (ite (v .> h)
                         (OldAnalysis.FSSet.elem (b - 1) v t)
                         (v .== h))
  where h = SL.head s
        t = SL.tail s

size :: Ord a => SymVal a => FSSet a -> SInteger
size = SL.length

delete :: Ord a => SymVal a => Integer -> SBV a -> FSSet a -> FSSet a
delete b v s
  | b < 0 = s
  | otherwise = ite (SL.null s)
                    []
                    (ite (v .< h)
                         s
                         (ite (v .== h)
                              t
                              (h .: delete (b - 1) v t)))
  where h = SL.head s
        t = SL.tail s

validAux :: Ord a => SymVal a => Integer -> SBV a -> FSSet a -> SBool
validAux b v s
  | b < 0 = sFalse
  | otherwise = ite (SL.null s)
                    sTrue
                    (ite (v .< h)
                         (validAux (b - 1) h t)
                         sFalse)
  where h = SL.head s
        t = SL.tail s

valid :: Ord a => SymVal a => Integer -> FSSet a -> SBool
valid b s
  | b < 0 = sFalse
  | otherwise = ite (SL.null s)
                    sTrue
                    (validAux b (SL.head s) (SL.tail s))


