module Language.PlutusNapkin
    ( head'
    , TermF (..)
    , Fix (..)
    , Term
    ) where

import           Language.PlutusNapkin.Type

head' :: [a] -> Maybe a
head' []    = Nothing
head' (x:_) = Just x
