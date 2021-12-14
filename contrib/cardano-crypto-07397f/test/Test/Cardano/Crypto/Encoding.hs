{-# LANGUAGE OverloadedStrings #-}

module Test.Cardano.Crypto.Encoding
    ( tests
    ) where

import Foundation.Check

import qualified Test.Cardano.Crypto.Encoding.Seed as Seed

tests :: Test
tests = Group "Encoding"
    [ Seed.tests
    ]
