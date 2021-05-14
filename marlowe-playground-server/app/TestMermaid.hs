{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main,
    )
    where

import           Escrow          (contract)
import           Marlowe.Mermaid (toMermaid)

main :: IO ()
main = putStrLn $ toMermaid contract
