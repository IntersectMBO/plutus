module Language.PlutusNapkin
    ( head'
    , Term (..)
    , Type (..)
    , Builtin (..)
    , Token (..)
    , Kind (..)
    -- * Parser
    , parse
    ) where

import           Language.PlutusNapkin.Parser
import           Language.PlutusNapkin.Type

head' :: [a] -> Maybe a
head' []    = Nothing
head' (x:_) = Just x
