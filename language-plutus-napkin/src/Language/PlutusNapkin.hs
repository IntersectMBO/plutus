module Language.PlutusNapkin
    ( head'
    , Term (..)
    , Type (..)
    , Builtin (..)
    , Name (..)
    , Kind (..)
    ) where

import           Language.PlutusNapkin.Type

head' :: [a] -> Maybe a
head' []    = Nothing
head' (x:_) = Just x
