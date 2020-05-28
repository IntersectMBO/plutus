{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -w #-}
module OldAnalysis.FSMap where

import           Data.SBV
import           Data.SBV.List  as SL
import           Data.SBV.Maybe as SM
import           Data.SBV.Tuple as ST
import           Prelude        hiding (all, lookup)

type NMap a b = [(a, b)]
type FSMap a b = SList (a, b)

empty :: Ord a => SymVal a => SymVal b => FSMap a b
empty = []

insert :: Ord a => SymVal a => SymVal b => Integer ->
          SBV a -> SBV b -> FSMap a b -> FSMap a b
insert b k v s
  | b < 0 = []
  | otherwise = ite (SL.null s)
                    (SL.singleton nh)
                    (ite (k .> h)
                         (oh .: insert (b - 1) k v t)
                         (ite (k .< h)
                              (nh .: s)
                              (nh .: t)))
  where oh = SL.head s
        (h, _) = ST.untuple oh
        t = SL.tail s
        nh = ST.tuple (k, v)

lookup :: Ord a => SymVal a => SymVal b => Integer ->
          SBV a -> FSMap a b -> SMaybe b
lookup b k s
  | b < 0 = sNothing
  | otherwise = ite (SL.null s)
                    SM.sNothing
                    (ite (k .> h)
                         (lookup (b - 1) k t)
                         (ite (k .== h)
                              (SM.sJust h2)
                              SM.sNothing))
  where (h, h2) = ST.untuple $ SL.head s
        t = SL.tail s

member :: Ord a => SymVal a => SymVal b => Integer ->
          SBV a -> FSMap a b -> SBool
member b k s = SM.isJust $ lookup b k s

findWithDefault :: Ord a => SymVal a => SymVal b => Integer ->
          SBV b -> SBV a -> FSMap a b -> SBV b
findWithDefault b def k s
  | b < 0 = def
  | otherwise = ite (SL.null s)
                    def
                    (ite (k .> h)
                         (findWithDefault (b - 1) def k t)
                         (ite (k .== h)
                              h2
                              def))
  where (h, h2) = ST.untuple $ SL.head s
        t = SL.tail s

size :: Ord a => SymVal a => SymVal b => FSMap a b -> SInteger
size = SL.length

delete :: Ord a => SymVal a => SymVal b => Integer ->
          SBV a -> FSMap a b -> FSMap a b
delete b v s
  | b < 0 = s
  | otherwise = ite (SL.null s)
                    []
                    (ite (v .< h1)
                         s
                         (ite (v .== h1)
                              t
                              (h .: delete (b - 1) v t)))
  where h = SL.head s
        (h1, _) = ST.untuple h
        t = SL.tail s

validAux :: Ord a => SymVal a => SymVal b => Integer -> SBV a -> FSMap a b -> SBool
validAux b v s
  | b < 0 = sFalse
  | otherwise = ite (SL.null s)
                    sTrue
                    (ite (v .< h)
                         (validAux (b - 1) h t)
                         sFalse)
  where (h, _) = ST.untuple $ SL.head s
        t = SL.tail s

valid :: Ord a => SymVal a => SymVal b => Integer -> FSMap a b -> SBool
valid b s
  | b < 0 = sFalse
  | otherwise = ite (SL.null s)
                    sTrue
                    (validAux b (fst $ ST.untuple $ SL.head s) (SL.tail s))

all :: Ord a => SymVal a => SymVal b => Integer -> (SBV b -> SBool) -> FSMap a b -> SBool
all b f s
  | b < 0 = sFalse
  | otherwise = ite (SL.null s)
                    sTrue
                    (f h .&& all (b - 1) f t)
  where (_, h) = ST.untuple $ SL.head s
        t = SL.tail s

unionWith :: Ord a => SymVal a => SymVal b => Integer ->
             (SBV b -> SBV b -> SBV b) -> FSMap a b -> FSMap a b -> FSMap a b
unionWith b f m1 m2
  | b < 0 = []
  | otherwise = ite (SL.null m1)
                    m2
                    (ite (SL.null m2)
                         m1
                         (ite (k1 .< k2)
                              (h1 .: unionWith (b - 1) f t1 m2)
                              (ite (k1 .> k2)
                                   (h2 .: unionWith (b - 1) f m1 t2)
                                   (nh .: unionWith (b - 1) f t1 t2))))
  where h1 = SL.head m1
        (k1, v1) = ST.untuple h1
        t1 = SL.tail m1
        h2 = SL.head m2
        (k2, v2) = ST.untuple h2
        t2 = SL.tail m2
        nh = ST.tuple (k1, f v1 v2)

minViewWithKey :: Ord a => SymVal a => SymVal b =>
                  FSMap a b -> SMaybe ((a, b), NMap a b)
minViewWithKey m =
  ite (SL.null m)
      SM.sNothing
      (SM.sJust (ST.tuple (SL.head m, SL.tail m)))

