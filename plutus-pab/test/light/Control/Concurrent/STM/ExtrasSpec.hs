{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Control.Concurrent.STM.ExtrasSpec
    ( tests
    ) where

import           Control.Concurrent            (threadDelay)
import           Control.Concurrent.Async      (concurrently, forConcurrently)
import           Control.Concurrent.STM        (atomically)
import           Control.Concurrent.STM.Extras
import           Control.Concurrent.STM.TVar   (newTVar, readTVar, writeTVar)
import           Control.Monad                 (forM_, void)
import           Control.Monad.IO.Class        (liftIO)
import           Data.Foldable                 (fold)
import           Data.Maybe                    (isNothing)
import           GHC.Conc.Sync                 (STM)
import           Test.Tasty                    (TestTree, defaultMain, testGroup)
import           Test.Tasty.HUnit              (HasCallStack, assertBool, assertEqual, testCase)

tests :: TestTree
tests =
    testGroup
        "Control.Concurrent.STM.ExtrasSpec - Stream tests"
        [ testCase "Can read one and only one" $ do
            let x :: STMStream Integer
                x = pure 5
            next <- readOne x
            assertEqual "" 5 (fst next)

            let next' = readOne <$> snd next
            assertBool "" (isNothing next')

        , testCase "Can read many" $ do
            let ns = [1..10]
                x :: STMStream Integer
                x = foldMap pure ns
            items <- readN 10 x
            assertEqual "" ns items

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
                  assertEqual "" [1,3] as

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
                  assertEqual "" [(1,1),(1,3)] as

            void $ forConcurrently [t1 [1,1,1,3] var1, t1 [1,3] var2, t3] id

        , testCase "Building streams from input with consecutive duplicates produce Streams with duplicates removed" $ do
            let x :: STMStream Integer
                x  = foldMap pure [1,1,1,3,3,4]
            items <- readN 3 x
            assertEqual "" [1,3,4] items

        , testCase "Combined streams don't produce interleaved duplicates" $ do
            let x, y :: STMStream Integer
                x  = foldMap pure [1,1,1,1,1,1]
                y  = foldMap pure [3,3,3,4]
                z  = foldMap pure [0,0,0,0]
                xs = fold [ x, z, y ]
            items <- readN 4 xs
            assertEqual "" [1,0,3,4] items
        ]
