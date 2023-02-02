module Main where

import Default

import Expr

import NonDefault

import Test.Tasty

import Universal

main :: IO ()
main = defaultMain $ testGroup "all"
    [ test_default
    , test_nonDefault
    , test_universal
    , test_expr
    ]
