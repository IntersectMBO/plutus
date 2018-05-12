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
    , Unique (..)
    , BuiltinName (..)
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
    -- * Helper functions
    , prettyText
    , compareName
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

prettyText :: Program a -> T.Text
prettyText = render . pretty

render :: Doc a -> T.Text
render = renderStrict . layoutSmart defaultLayoutOptions

format :: BSL.ByteString -> Either ParseError T.Text
format = fmap render . formatDoc
