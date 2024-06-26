```
{-# OPTIONS --cubical-compatible --no-universe-polymorphism
            --no-sized-types --no-guardedness --level-universe #-}

module Utils.Bool where

data Bool : Set where
  false true : Bool
{-# COMPILE GHC Bool = data Bool (True | False) #-}