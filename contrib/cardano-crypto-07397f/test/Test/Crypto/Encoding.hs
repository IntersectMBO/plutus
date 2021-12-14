{-# LANGUAGE OverloadedStrings #-}

module Test.Crypto.Encoding
    ( tests
    ) where

import Foundation.Check

import qualified Test.Crypto.Encoding.BIP39 as BIP39

tests :: Test
tests = Group "Encoding"
    [ BIP39.tests
    ]
