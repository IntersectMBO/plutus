{-# LANGUAGE NoImplicitPrelude #-}

module Test.Data.List
    ( generateListOfElement
    , generateListOfElementMaxN
    , generateNonEmptyListOfElement
    , RandomList(..)
    ) where

import Foundation
import Foundation.Collection (nonEmpty_, NonEmpty)
import Foundation.Check
import Foundation.Monad

import Basement.From (from)
import Basement.Cast (cast)

-- | convenient function to replicate thegiven Generator of `e` a randomly
-- choosen amount of time.
generateListOfElement :: Gen e -> Gen [e]
generateListOfElement = generateListOfElementMaxN 100

-- | convenient function to generate up to a certain amount of time the given
-- generator.
generateListOfElementMaxN :: CountOf e -> Gen e -> Gen [e]
generateListOfElementMaxN n e = replicateBetween 0 (from n) e

generateNonEmptyListOfElement :: CountOf e -> Gen e -> Gen (NonEmpty [e])
generateNonEmptyListOfElement n e = nonEmpty_ <$> replicateBetween 1 (from n) e

data RandomList = RandomList [Int]
    deriving (Show,Eq)

instance Arbitrary RandomList where
    arbitrary = RandomList <$> replicateBetween 100 400 (cast <$> between (0,8))

replicateBetween n1 n2 f =
    between (n1, n2) >>= \n -> replicateM (CountOf (toInt n)) f
  where
    toInt :: Word -> Int
    toInt = cast
