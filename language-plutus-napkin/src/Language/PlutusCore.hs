module Language.PlutusCore
    ( -- * AST
      Term (..)
    , Type (..)
    , Builtin (..)
    , Kind (..)
    , ParseError (..)
    , Version (..)
    , Program (..)
    , Name (..)
    , Special (..)
    , Unique
    -- * Lexer
    , AlexPosn (..)
    , Token (..)
    -- * Parser
    , parse
    -- * Formatter
    , format
    , formatDoc
    -- * Base functors
    , TermF (..)
    , TypeF (..)
    ) where

import qualified Data.ByteString.Lazy                  as BSL
import qualified Data.Text                             as T
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import           Language.PlutusCore.Identifier
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Type

formatDoc :: BSL.ByteString -> Either ParseError (Doc a)
formatDoc = fmap pretty . parse

format :: BSL.ByteString -> Either ParseError T.Text
format = fmap (renderStrict . layoutSmart defaultLayoutOptions) . formatDoc
