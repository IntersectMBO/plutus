module Language.PlutusCore
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
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Parser
import           Language.PlutusCore.PrettyPrint
import           Language.PlutusCore.Type

format :: BSL.ByteString -> Either ParseError BSL.ByteString
format = (g . prettyPrint) <=< parse
    where g (Just x) = Right x
          g Nothing  = Left InternalError
