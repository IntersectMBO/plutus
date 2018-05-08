module Language.PlutusCore
    ( -- * Types
      Term (..)
    , Type (..)
    , Builtin (..)
    , Token (..)
    , Kind (..)
    , AlexPosn (..)
    , ParseError (..)
    -- * Parser
    , parse
    -- * Formatter
    , format
    -- * Base functors
    , TermF (..)
    , TypeF (..)
    ) where

import           Control.Monad                   ((<=<))
import qualified Data.ByteString.Lazy            as BSL
import           Data.Text.Prettyprint.Doc
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Parser
import           Language.PlutusCore.PrettyPrint
import           Language.PlutusCore.Type

format :: BSL.ByteString -> Either ParseError (Doc a)
format = fmap pretty . rewrite <=< parse
