{-# LANGUAGE OverloadedStrings #-}

module Test.Cardano
    ( tests
    ) where

import Foundation.Check

import qualified Test.Cardano.Crypto as Crypto

tests :: Test
tests = Group "Cardano"
    [ Crypto.tests
    ]
