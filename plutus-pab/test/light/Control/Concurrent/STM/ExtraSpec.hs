{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Control.Concurrent.STM.ExtraSpec
    ( tests
    ) where

import           Control.Concurrent           (threadDelay)
import           Control.Concurrent.Async     (concurrently, forConcurrently)
import           Control.Concurrent.STM       (atomically)
import           Control.Concurrent.STM.Extra
import           Control.Concurrent.STM.TVar  (newTVar, readTVar, writeTVar)
import           Control.Monad                (forM_, void)
import           Control.Monad.IO.Class       (liftIO)
import           Data.Foldable                (fold)
import           Data.Maybe                   (isNothing)
import           GHC.Conc.Sync                (STM)
import           Test.Tasty                   (TestTree, defaultMain, testGroup)
import           Test.Tasty.HUnit             (HasCallStack, assertBool, assertEqual, testCase)

tests :: TestTree
tests =
    testGroup
        "Control.Concurrent.STM.ExtraSpec"
        [ testCase "Can read one and only one" $ do
            let x :: STMStream Integer
                x = pure 5
            next <- readOne x
            assertEqual "Couldn't read one!" 5 (fst next)

            let next' = readOne <$> snd next
            assertBool "Found more than one!" (isNothing next')

        , testCase "Can read many" $ do
            let ns = [1..10]
                x :: STMStream Integer
                x = foldMap pure ns
            items <- readN 10 x
            assertEqual "Couldn't read what we wrote!" ns items

        , testCase "Unfold doesn't yield consecutive duplicates" $ do
            var <- liftIO $ atomically $ newTVar 1

            -- Two threads:
            -- 1. Constantly write duplicate values
            let t1 = forM_ [1,1,1,3] $ \a -> do
                  atomically $ writeTVar var a
                  threadDelay 1_000
            --
            -- 2. Constantly read; hopefully no dupes.
                t2 = do
                  let s = unfold $ readTVar var
                  as <- readN 2 s
                  assertEqual "Stream didn't remove consecutive duplicates" [1,3] as

            void $ concurrently t1 t2

        , testCase "Applicatively-constructed stream doesn't yield consecutive duplicates" $ do
            var1 <- liftIO $ atomically $ newTVar 1
            var2 <- liftIO $ atomically $ newTVar 1

            let t1 as var = forM_ as $ \a -> do
                  atomically $ writeTVar var a
                  threadDelay 1_000

                t3 = do
                  let s = unfold $ ((,) <$> readTVar var1 <*> readTVar var2)
                  as <- readN 2 s
                  assertEqual "Stream didn't remove consecutive duplicates" [(1,1),(1,3)] as

            void $ forConcurrently [t1 [1,1,1,3] var1, t1 [1,3] var2, t3] id

        , testCase "Dedupe removes consecutive duplicates" $ do
            let x :: STMStream Integer
                x  = foldMap pure [1,1,1,3]
                xs = dedupe x
            items <- readN 2 xs
            assertEqual "Dedupe yielded duplicates." [1,3] items

        , testCase "Fold doesn't give consecutive duplicates" $ do
            let x, y :: STMStream Integer
                x  = foldMap pure [1,1,1,1,1,1]
                y  = foldMap pure [3,3,3,4]
                xs = fold [ x, y ]
            items <- readN 3 xs
            assertEqual "Fold yielded duplicates." [1,3,4] items
        ]
