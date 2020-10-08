{-# LANGUAGE OverloadedStrings #-}
module Example where

import           Language.Marlowe

main :: IO ()
main = print . pretty $ contract


{- Define a contract, Close is the simplest contract which just ends the contract straight away
-}

contract :: Contract

contract = Close
