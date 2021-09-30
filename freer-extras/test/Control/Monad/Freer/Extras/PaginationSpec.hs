{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE OverloadedStrings #-}

module Control.Monad.Freer.Extras.PaginationSpec (tests) where

import           Control.Monad                         (forM_)
import           Control.Monad.Freer.Extras.Pagination (Page (nextPageQuery, pageItems), PageQuery (PageQuery), pageOf)
import           Data.List                             (sort)
import           Data.Maybe                            (listToMaybe)
import           Data.Set                              (Set)
import qualified Data.Set                              as Set
import           Hedgehog                              (Property, forAll, property, (===))
import qualified Hedgehog
import           Hedgehog.Gen                          as Gen
import           Hedgehog.Range                        as Gen
import           Test.Tasty
import           Test.Tasty.Hedgehog                   (testProperty)

tests :: TestTree
tests = do
  testGroup "pagination"
    [ testGroup "pageOf"
        [ testProperty "size of pageItems of all pages should be less or equal than total number of items in list"
                       pageItemsSizeLessOrEqualGenItemsSizeSpec
        , testProperty "size of pageItems of all pages should be less or equal than requested page size"
                       pageItemsSizeLessOrEqualThanRequestedPageSize
        , testProperty "last page should have no next page"
                      lastPageShouldHaveNoNextPageQuerySpec
        , testProperty "concat items for all pages should be the same as generated items"
                       pageItemsEqualGenItemsSpec
        , testProperty "page items should be sorted in ascending order"
                       pageItemsSortedAscOrderSpec
        , testProperty "page size equal to total number of items in list should return a single page"
                       pageSizeEqualToTotalItemsSizeShouldReturnOnePage
        ]
    ]

-- | The length of field 'pageItems' should be less or equal than total number
-- of items.
pageItemsSizeLessOrEqualGenItemsSizeSpec :: Property
pageItemsSizeLessOrEqualGenItemsSizeSpec = property $ do
  items <- forAll $ Gen.set (Gen.linear 1 10) $ Gen.int (Gen.linear 0 100)
  pageSize <- forAll $ Gen.int (Gen.linear 1 20)
  forM_ (getAllPages (PageQuery (fromIntegral pageSize) Nothing) items) $ \page -> do
    Hedgehog.assert $ length (pageItems page) <= length items

-- | The length of field 'pageItems' should be less or equal than the requested
-- 'PageSize'.
pageItemsSizeLessOrEqualThanRequestedPageSize :: Property
pageItemsSizeLessOrEqualThanRequestedPageSize = property $ do
  items <- forAll $ Gen.set (Gen.linear 1 10) $ Gen.int (Gen.linear 0 100)
  pageSize <- forAll $ Gen.int (Gen.linear 1 20)
  forM_ (getAllPages (PageQuery (fromIntegral pageSize) Nothing) items) $ \page -> do
    Hedgehog.assert $ length (pageItems page) <= pageSize

-- | The last 'Page' should have a number of page items less or equal than
-- requested 'PageSize' and it's 'nextPageQuery' field should be Nothing.
lastPageShouldHaveNoNextPageQuerySpec :: Property
lastPageShouldHaveNoNextPageQuerySpec = property $ do
  items <- forAll $ Gen.set (Gen.linear 1 10) $ Gen.int (Gen.linear 0 100)
  pageSize <- forAll $ Gen.int (Gen.linear 1 20)
  let lastPageM = listToMaybe $ reverse $ getAllPages (PageQuery (fromIntegral pageSize) Nothing) items
  case lastPageM of
    Nothing -> Hedgehog.assert False
    Just lastPage -> do
      Hedgehog.assert $ length (pageItems lastPage) <= pageSize
      nextPageQuery lastPage === Nothing

-- | Concatenating all 'pageItems' of all 'Page's should be equal to the
-- generated input list.
pageItemsEqualGenItemsSpec :: Property
pageItemsEqualGenItemsSpec = property $ do
  items <- forAll $ Gen.set (Gen.linear 1 10) $ Gen.int (Gen.linear 0 100)
  let pages = getAllPages (PageQuery 1 Nothing) items
  Set.fromList (concatMap pageItems pages) === Set.fromList (Set.toList items)

-- | The elemens in all 'pageItems' of all 'Page's should be sorted in
-- ascending order.
pageItemsSortedAscOrderSpec :: Property
pageItemsSortedAscOrderSpec = property $ do
  items <- forAll $ Gen.set (Gen.linear 1 10) $ Gen.int (Gen.linear 0 100)
  let pages = getAllPages (PageQuery 1 Nothing) items
  concatMap pageItems pages === sort (concatMap pageItems pages)

pageSizeEqualToTotalItemsSizeShouldReturnOnePage :: Property
pageSizeEqualToTotalItemsSizeShouldReturnOnePage = property $ do
  items <- forAll $ Gen.set (Gen.linear 1 10) $ Gen.int (Gen.linear 0 100)
  let pages = getAllPages (PageQuery (fromIntegral $ length items) Nothing) items
  length pages === 1

getAllPages
    :: (Eq a)
    => PageQuery a
    -> Set a
    -> [Page a]
getAllPages pq items =
  let page = pageOf pq items
   in case nextPageQuery page of
    Nothing -> [page]
    Just newPageQuery -> do
      let nextPages = getAllPages newPageQuery items
      page : nextPages
