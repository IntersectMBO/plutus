{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Main(main) where

import qualified Control.Monad.Freer.Extras.BeamSpec       as BeamSpec
import qualified Control.Monad.Freer.Extras.PaginationSpec as PaginationSpec

import           Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup "tests"
    [ BeamSpec.tests
    , PaginationSpec.tests
    ]

