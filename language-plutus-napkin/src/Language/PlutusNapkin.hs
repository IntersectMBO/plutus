module Language.PlutusNapkin
    ( Term (..)
    , Type (..)
    , Builtin (..)
    , Token (..)
    , Kind (..)
    , AlexPosn (..)
    , ParseError (..)
    -- * Parser
    , parse
    -- * Pretty-printer
    , prettyPrint
    -- * Formatter
    , format
    ) where

import           Control.Monad                     ((<=<))
import qualified Data.ByteString.Lazy              as BSL
import           Language.PlutusNapkin.Lexer
import           Language.PlutusNapkin.Parser
import           Language.PlutusNapkin.PrettyPrint
import           Language.PlutusNapkin.Type

format :: BSL.ByteString -> Either ParseError BSL.ByteString
format = (g . prettyPrint) <=< parse
    where g (Just x) = Right x
          g Nothing  = Left InternalError
