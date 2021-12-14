{-# LANGUAGE OverloadedStrings #-}

module Test.Crypto
    ( tests
    ) where

import Foundation.Check

import qualified Test.Crypto.Encoding as Encoding

tests :: Test
tests = Group "Crypto"
    [ Encoding.tests
    ]
