module Language.PlutusCore
    ( -- * Types
      Term (..)
    , Type (..)
    , Builtin (..)
    , Token (..)
    , Kind (..)
    , AlexPosn (..)
    , ParseError (..)
    , Version (..)
    , Program (..)
    -- * Parser
    , parse
    -- * Formatter
    , format
    , formatDoc
    -- * Base functors
    , TermF (..)
    , TypeF (..)
    ) where

import           Control.Monad                         ((<=<))
import qualified Data.ByteString.Lazy                  as BSL
import qualified Data.Text                             as T
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Parser
import           Language.PlutusCore.PrettyPrint
import           Language.PlutusCore.Type

formatDoc :: BSL.ByteString -> Either ParseError (Doc a)
formatDoc = fmap pretty . rewriteTerm <=< parse

format :: BSL.ByteString -> Either ParseError T.Text
format = fmap (renderStrict . layoutSmart defaultLayoutOptions) . formatDoc
