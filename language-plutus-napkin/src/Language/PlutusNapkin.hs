module Language.PlutusNapkin
    ( head'
    , Term (..)
    , Type (..)
    , Builtin (..)
    , Token (..)
    , Kind (..)
    -- * Lexer
    , alexMonadScan
    , runAlex
    , alexEOF
    ) where

import           Language.PlutusNapkin.Lexer
import           Language.PlutusNapkin.Type

head' :: [a] -> Maybe a
head' []    = Nothing
head' (x:_) = Just x
