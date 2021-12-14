{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Test.Foundation.Conduit
  ( testConduit
  ) where

import Foundation
import Foundation.Check
import Foundation.Conduit
import Foundation.IO

testConduit :: Test
testConduit = Group "Conduit"
    [ CheckPlan "sourceHandle gives same data as readFile" testSourceFile
    , CheckPlan "sourceHandle/sinkHandle copies data" testCopyFile
    , CheckPlan "sourceFile/sinkFile copies data" testCopyFileRes
    ]
  where
    --testSourceFile :: Assertion
    testSourceFile = do
        let fp = "foundation.cabal"
        arrs <- pick "conduit-read" $ withFile fp ReadMode $ \h ->
                                          runConduit $ sourceHandle h .| sinkList
        arr <- pick "read-source" $ readFile fp
        validate "foundation.cabal contents" $ arr == (mconcat arrs)

    --testCopyFile :: Assertion
    testCopyFile = do
        let src = "foundation.cabal"
            dst = "temp-file" -- FIXME some temp file API?
        pick "conduit-duplicate" $ withFile src ReadMode $ \hin ->
                                   withFile dst WriteMode $ \hout ->
                                       runConduit $ sourceHandle hin .| sinkHandle hout
        orig <- pick "read-source" $ readFile src
        new <- pick "read-destination" $ readFile dst
        validate "copied foundation.cabal contents" $ orig == new

    --testCopyFileRes :: Assertion
    testCopyFileRes = do
        let src = "foundation.cabal"
            dst = "temp-file" -- FIXME some temp file API?
        pick "conduit-res" $ runConduitRes $ sourceFile src .| sinkFile dst
        orig <- pick "read-soure" $ readFile src
        new <- pick "read-destination" $ readFile dst
        validate "copied foundation.cabal contents" $ orig == new
