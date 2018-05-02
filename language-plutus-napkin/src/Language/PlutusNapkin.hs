module Language.PlutusNapkin
    ( head'
    , PlutusNapkin (..)
    ) where

import           Language.PlutusNapkin.Type

head' :: [a] -> Maybe a
head' []    = Nothing
head' (x:_) = Just x
