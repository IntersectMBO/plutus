-- |
-- Module      : Test.Checks.Property.Collection
-- License     : BSD-style
-- Maintainer  : Nicolas Di Prima <nicolas@primetype.co.uk>
-- Stability   : stable
-- Portability : portable
--
-- This module contains all the different property tests for the Foundation's
-- collection classes.
--
-- You can either run all the collection property tests with the
-- @collectionProperties@ function or run them individually.
--

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Checks.Property.Collection
    ( collectionProperties

    , -- * properties per class
      testEqualityProperties
    , testOrderingProperties
    , testIsListPropertyies
    , testMonoidProperties
    , testCollectionProperties
    , testSequentialProperties
    , fromListP
    , toListP
    ) where

import Foundation
import Foundation.Collection
import Foundation.Check

import Control.Monad (replicateM)
import qualified Prelude (replicate)

-- | convenient function to replicate thegiven Generator of `e` a randomly
-- choosen amount of time.
generateListOfElement :: Gen e -> Gen [e]
generateListOfElement = generateListOfElementMaxN 100

-- | convenient function to generate up to a certain amount of time the given
-- generator.
generateListOfElementMaxN :: Word -> Gen e -> Gen [e]
generateListOfElementMaxN n e = between (0,n) >>= flip replicateM e . fromIntegral

generateNonEmptyListOfElement :: Word -> Gen e -> Gen (NonEmpty [e])
generateNonEmptyListOfElement n e = nonEmpty_ <$> (between (1,n) >>= flip replicateM e . fromIntegral)

-- | internal helper to convert a list of element into a collection
--
fromListP :: (IsList c, Item c ~ Element c) => Proxy c -> [Element c] -> c
fromListP p = \x -> asProxyTypeOf (fromList x) p

fromListNonEmptyP :: Collection a => Proxy a -> NonEmpty [Element a] -> NonEmpty a
fromListNonEmptyP proxy = nonEmpty_ . fromListP proxy . getNonEmpty

-- | internal helper to convert a given Collection into a list of its element
--
toListP :: (IsList c, Item c ~ Element c) => Proxy c -> c -> [Element c]
toListP p x = toList (asProxyTypeOf x p)

-- | test all the diffent classes of a Foundation's collection class
--
-- * testEqualityProperties
-- * testOrderingProperties
-- * testIsListPropertyies
-- * testMonoidProperties
-- * testCollectionProperties
-- * testSequentialProperties
--
collectionProperties :: forall collection
                      . ( Sequential collection
                        , Typeable collection, Typeable (Element collection)
                        , Eq collection,   Eq (Element collection)
                        , Show collection, Show (Element collection)
                        , Ord collection,  Ord (Element collection)
                        )
                     => String
                     -> Proxy collection
                     -> Gen (Element collection)
                     -> Test
collectionProperties name proxy genElement = Group name
    [ testEqualityProperties   proxy genElement
    , testOrderingProperties   proxy genElement
    , testIsListPropertyies    proxy genElement
    , testMonoidProperties     proxy genElement
    , testCollectionProperties proxy genElement
    , testSequentialProperties proxy genElement
    ]

-- | test property equality for the given Collection
--
-- This does to enforce
testEqualityProperties :: forall collection
                        . ( IsList collection
                          , Element collection ~ Item collection
                          , Typeable collection
                          , Eq collection,   Eq (Element collection)
                          , Show collection, Show (Element collection)
                          , Ord collection,  Ord (Element collection)
                          )
                       => Proxy collection
                       -> Gen (Element collection)
                       -> Test
testEqualityProperties proxy genElement = Group "equality"
    [ Property "x == x" $ withElements $ \l -> let col = fromListP proxy l in col === col
    , Property "x == y" $ with2Elements $ \(l1, l2) ->
        (fromListP proxy l1 == fromListP proxy l2) === (l1 == l2)
    ]
  where
    withElements f = forAll (generateListOfElement genElement) f
    with2Elements f = forAll ((,) <$> generateListOfElement genElement <*> generateListOfElement genElement) f


testOrderingProperties :: forall collection
                        . ( IsList collection
                          , Element collection ~ Item collection
                          , Typeable collection
                          , Eq collection,   Eq (Element collection)
                          , Show collection, Show (Element collection)
                          , Ord collection,  Ord (Element collection)
                          )
                       => Proxy collection
                       -> Gen (Element collection)
                       -> Test
testOrderingProperties proxy genElement = Group "ordering"
    [ Property "x `compare` y" $ with2Elements $ \(l1, l2) ->
        (fromListP proxy l1 `compare` fromListP proxy l2) === (l1 `compare` l2)
    ]
  where
    with2Elements f = forAll ((,) <$> generateListOfElement genElement <*> generateListOfElement genElement) f

testIsListPropertyies :: forall collection
                       . ( IsList collection, Eq collection, Show collection
                         , Typeable collection, Typeable (Element collection)
                         , Element collection ~ Item collection
                         , Eq (Item collection), Show (Item collection)
                         )
                      => Proxy collection
                      -> Gen (Element collection)
                      -> Test
testIsListPropertyies proxy genElement = Group "IsList"
    [ Property "fromList . toList == id" $ withElements $ \l -> (toList $ fromListP proxy l) === l
    ]
  where
    withElements f = forAll (generateListOfElement genElement) f

testMonoidProperties :: forall collection
                      . ( Monoid collection, IsList collection, Eq collection, Show collection
                        , Typeable collection, Typeable (Element collection)
                        , Element collection ~ Item collection
                        , Eq (Item collection), Show (Item collection)
                        )
                     => Proxy collection
                     -> Gen (Element collection)
                     -> Test
testMonoidProperties proxy genElement = Group "Monoid"
    [ Property "mempty <> x == x" $ withElements $ \l -> let col = fromListP proxy l in (col <> mempty) === col
    , Property "x <> mempty == x" $ withElements $ \l -> let col = fromListP proxy l in (mempty <> col) === col
    , Property "x1 <> x2 == x1|x2" $ with2Elements $ \(l1,l2) ->
        (fromListP proxy l1 <> fromListP proxy l2) === fromListP proxy (l1 <> l2)
    , Property "mconcat [map fromList [e]] = fromList (concat [e])" $ withNElements $ \l ->
        mconcat (fmap (fromListP proxy) l) === fromListP proxy (mconcat l)
    ]
  where
    withElements f = forAll (generateListOfElement genElement) f
    with2Elements f = forAll ((,) <$> generateListOfElement genElement <*> generateListOfElement genElement) f
    withNElements f = forAll (generateListOfElementMaxN 5 (generateListOfElement genElement)) f

-- | test the Foundation's @Collection@ class.
--
testCollectionProperties :: forall collection
                          . ( Collection collection
                            , Typeable collection, Typeable (Element collection)
                            , Show (Element collection), Eq (Element collection)
                                                       , Ord (Element collection)
                            , Ord collection
                            )
                         => Proxy collection
                            -- ^ a proxy for the collection to test
                         -> Gen (Element collection)
                            -- ^ a generator to generate elements for the collection
                         -> Test
testCollectionProperties proxy genElement = Group "Collection"
    [ Property "null mempty" $ (null $ fromListP proxy []) === True
    , Property "null . getNonEmpty" $ withNonEmptyElements $ \els ->
          (null $ fromListP proxy $ getNonEmpty els) === False
    , Property "length" $ withElements $ \l -> (length $ fromListP proxy l) === length l
    , Property "elem" $ withListAndElement $ \(l,e) -> elem e (fromListP proxy l) === elem e l
    , Property "notElem" $ withListAndElement $ \(l,e) -> notElem e (fromListP proxy l) === notElem e l
    , Property "minimum" $ withNonEmptyElements $ \els -> minimum (fromListNonEmptyP proxy els) === minimum els
    , Property "maximum" $ withNonEmptyElements $ \els -> maximum (fromListNonEmptyP proxy els) === maximum els
    , Property "all" $ withListAndElement $ \(l, e) ->
        (all (/= e) (fromListP proxy l) === all (/= e) l) `propertyAnd`
        (all (== e) (fromListP proxy l) === all (== e) l)
    , Property "any" $ withListAndElement $ \(l, e) ->
        (any (/= e) (fromListP proxy l) === any (/= e) l) `propertyAnd`
        (any (== e) (fromListP proxy l) === any (== e) l)
    ]
  where
    withElements f = forAll (generateListOfElement genElement) f
    withListAndElement = forAll ((,) <$> generateListOfElement genElement <*> genElement)
    withNonEmptyElements f = forAll (generateNonEmptyListOfElement 80 genElement) f

testSequentialProperties :: forall collection
                          . ( Sequential collection
                            , Typeable collection, Typeable (Element collection)
                            , Eq collection, Eq (Element collection)
                            , Ord collection, Ord (Element collection)
                            , Show collection, Show (Element collection)
                            )
                         => Proxy collection
                         -> Gen (Element collection)
                         -> Test
testSequentialProperties proxy genElement = Group "Sequential"
    [ Property "take" $ withElements2 $ \(l, n) -> toList (take n $ fromListP proxy l) === (take n) l
    , Property "drop" $ withElements2 $ \(l, n) -> toList (drop n $ fromListP proxy l) === (drop n) l
    , Property "splitAt" $ withElements2 $ \(l, n) -> toList2 (splitAt n $ fromListP proxy l) === (splitAt n) l
    , Property "revTake" $ withElements2 $ \(l, n) -> toList (revTake n $ fromListP proxy l) === (revTake n) l
    , Property "revDrop" $ withElements2 $ \(l, n) -> toList (revDrop n $ fromListP proxy l) === (revDrop n) l
    , Property "revSplitAt" $ withElements2 $ \(l, n) -> toList2 (revSplitAt n $ fromListP proxy l) === (revSplitAt n) l
    , Property "break" $ withElements2E $ \(l, c) -> toList2 (break (== c) $ fromListP proxy l) === (break (== c)) l
    , Property "breakEnd" $ withElements2E $ \(l, c) -> toList2 (breakEnd (== c) $ fromListP proxy l) === (breakEnd (== c)) l
    , Property "breakElem" $ withElements2E $ \(l, c) -> toList2 (breakElem c $ fromListP proxy l) === (breakElem c) l
    , Property "span" $ withElements2E $ \(l, c) -> toList2 (span (== c) $ fromListP proxy l) === (span (== c)) l
    , Property "spanEnd" $ withElements2E $ \(l, c) -> toList2 (spanEnd (== c) $ fromListP proxy l) === (spanEnd (== c)) l
    , Property "filter" $ withElements2E $ \(l, c) -> toList (filter (== c) $ fromListP proxy l) === (filter (== c)) l
    , Property "partition" $ withElements2E $ \(l, c) -> toList2 (partition (== c) $ fromListP proxy l) === (partition (== c)) l
    , Property "snoc" $ withElements2E $ \(l, c) -> toList (snoc (fromListP proxy l) c) === (l <> [c])
    , Property "cons" $ withElements2E $ \(l, c) -> toList (cons c (fromListP proxy l)) === (c : l)
    , Property "unsnoc" $ withElements $ \l -> fmap toListFirst (unsnoc (fromListP proxy l)) === unsnoc l
    , Property "uncons" $ withElements $ \l -> fmap toListSecond (uncons (fromListP proxy l)) === uncons l
    , Property "head" $ withNonEmptyElements $ \els -> head (fromListNonEmptyP proxy els) === head els
    , Property "last" $ withNonEmptyElements $ \els -> last (fromListNonEmptyP proxy els) === last els
    , Property "tail" $ withNonEmptyElements $ \els -> toList (tail $ fromListNonEmptyP proxy els) === tail els
    , Property "init" $ withNonEmptyElements $ \els -> toList (init $ fromListNonEmptyP proxy els) === init els
    , Property "splitOn" $ withElements2E $ \(l, ch) ->
         fmap toList (splitOn (== ch) (fromListP proxy l)) === splitOn (== ch) l
    , testSplitOn proxy (const True) mempty
    , Property "intercalate c (splitOn (c ==) col) == col" $ withElements2E $ \(c, ch) ->
        intercalate [ch] (splitOn (== ch) c) === c
    , Property "intercalate c (splitOn (c ==) (col ++ [c]) == (col ++ [c])" $ withElements2E $ \(c, ch) ->
        intercalate [ch] (splitOn (== ch) $ snoc c ch) === (snoc c ch)
    , Property "intercalate c (splitOn (c ==) (col ++ [c,c]) == (col ++ [c,c])" $ withElements2E $ \(c, ch) ->
        intercalate [ch] (splitOn (== ch) $ snoc (snoc c ch) ch) === (snoc (snoc c ch) ch)
    , Property "intersperse" $ withElements2E $ \(l, c) ->
        toList (intersperse c (fromListP proxy l)) === intersperse c l
    , Property "intercalate" $ withElements2E $ \(l, c) ->
        let ls = Prelude.replicate 5 l
            cs = Prelude.replicate 5 c
        in toList (intercalate (fromListP proxy cs) (fromListP proxy <$> ls)) === intercalate cs ls
    , Property "sortBy" $ withElements $ \l ->
        (sortBy compare $ fromListP proxy l) === fromListP proxy (sortBy compare l)
    , Property "reverse" $ withElements $ \l ->
        (reverse $ fromListP proxy l) === fromListP proxy (reverse l)
    -- stress slicing
    , Property "take . take" $ withElements3 $ \(l, n1, n2) -> toList (take n2 $ take n1 $ fromListP proxy l) === (take n2 $ take n1 l)
    , Property "drop . take" $ withElements3 $ \(l, n1, n2) -> toList (drop n2 $ take n1 $ fromListP proxy l) === (drop n2 $ take n1 l)
    , Property "drop . drop" $ withElements3 $ \(l, n1, n2) -> toList (drop n2 $ drop n1 $ fromListP proxy l) === (drop n2 $ drop n1 l)
    , Property "drop . take" $ withElements3 $ \(l, n1, n2) -> toList (drop n2 $ take n1 $ fromListP proxy l) === (drop n2 $ take n1 l)
    , Property "second take . splitAt" $ withElements3 $ \(l, n1, n2) ->
        (toList2 $ (second (take n1) . splitAt n2) $ fromListP proxy l) === (second (take n1) . splitAt n2) l
    , Property "splitAt == (take, drop)" $ withCollection2 $ \(col, n) ->
        splitAt n col === (take n col, drop n col)
    , Property "revSplitAt == (revTake, revDrop)" $ withCollection2 $ \(col, n) ->
        revSplitAt n col === (revTake n col, revDrop n col)
    , Group "isSuffixOf"
        [ Property "collection + sub" $ withElements2 $ \(l1, n) ->
            let c1 = fromListP proxy l1 in isSuffixOf (revTake n c1) c1 === isSuffixOf (revTake n l1) l1
        , Property "2 collections" $ with2Elements $ \(l1, l2) -> isSuffixOf (fromListP proxy l1) (fromListP proxy l2) === isSuffixOf l1 l2
        , Property "collection + empty" $ withElements $ \l1 ->
            isSuffixOf (fromListP proxy []) (fromListP proxy l1) === isSuffixOf [] l1
        ]
    , Group "isPrefixOf"
        [ Property "collection + sub" $ withElements2 $ \(l1, n) ->
            let c1 = fromListP proxy l1 in isPrefixOf (take n c1) c1 === isPrefixOf (take n l1) l1
        , Property "2 collections" $ with2Elements $ \(l1, l2) -> isPrefixOf (fromListP proxy l1) (fromListP proxy l2) === isPrefixOf l1 l2
        , Property "collection + empty" $ withElements $ \l1 ->
            isPrefixOf (fromListP proxy []) (fromListP proxy l1) === isPrefixOf [] l1
        ]
    , Group "isInfixOf"
        [ Property "b isInfixOf 'a b c'" $ with3Elements $ \(a, b, c) -> 
            isInfixOf (toCol b) (toCol a <> toCol b <> toCol c)
        , Property "the reverse is typically not an infix" $ withElements $ \a' ->
            let a = toCol a'; rev = reverse a in isInfixOf rev a === (a == rev)
        ]
    ]
{-
    , testProperty "imap" $ \(CharMap (LUString u) i) ->
        (imap (addChar i) (fromList u) :: String) `assertEq` fromList (Prelude.map (addChar i) u)
    ]
-}
  where
    toCol = fromListP proxy 
    toList2 (x,y) = (toList x, toList y)
    toListFirst (x,y) = (toList x, y)
    toListSecond (x,y) = (x, toList y)
    withElements f = forAll (generateListOfElement genElement) f
    with2Elements f = forAll ((,) <$> generateListOfElement genElement <*> generateListOfElement genElement) f
    with3Elements f = forAll ((,,) <$> generateListOfElement genElement <*> generateListOfElement genElement <*> generateListOfElement genElement) f
    withElements2 f = forAll ((,) <$> generateListOfElement genElement <*> arbitrary) f
    withElements3 f = forAll ((,,) <$> generateListOfElement genElement <*> arbitrary <*> arbitrary) f
    withElements2E f = forAll ((,) <$> generateListOfElement genElement <*> genElement) f
    withNonEmptyElements f = forAll (generateNonEmptyListOfElement 80 genElement) f
    withCollection2 f = forAll ((,) <$> (fromListP proxy <$> generateListOfElement genElement) <*> arbitrary) f

    testSplitOn :: ( Sequential a
                   , Show a, Show (Element a)
                   , Typeable a
                   , Eq (Element a)
                   , Eq a, Ord a, Ord (Item a), Show a
                   )
                => Proxy a -> (Element a -> Bool) -> a
                -> Test
    testSplitOn _ predicate col = Property "splitOn (const True) mempty == [mempty]" $
      (splitOn predicate col) === [col]
