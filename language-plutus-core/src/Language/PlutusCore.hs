module Language.PlutusCore
    ( -- * Parser
      parse
    -- * Pretty-printing
    , prettyText
    -- * Type checking
    , kindCheck
    , typeCheck
    , annotate
    -- * AST
    , Term (..)
    , Type (..)
    , Constant (..)
    , Kind (..)
    , ParseError (..)
    , Version (..)
    , Program (..)
    , Name (..)
    , Unique (..)
    , BuiltinName (..)
    , TypeBuiltin (..)
    -- * Lexer
    , AlexPosn (..)
    -- * Type-checking types
    , TypeAnnot
    , KindAnnot
    , TypeError (..)
    -- * Formatting
    , format
    , formatDoc
    -- * Base functors
    , TermF (..)
    , TypeF (..)
    ) where

import qualified Data.ByteString.Lazy                  as BSL
import qualified Data.Text                             as T
import           Data.Text.Prettyprint.Doc             hiding (annotate)
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeRenamer

formatDoc :: BSL.ByteString -> Either ParseError (Doc a)
formatDoc = fmap pretty . parse

-- | Render a 'Program' as strict 'Text'.
prettyText :: Program a -> T.Text
prettyText = render . pretty

render :: Doc a -> T.Text
render = renderStrict . layoutSmart defaultLayoutOptions

format :: BSL.ByteString -> Either ParseError T.Text
format = fmap render . formatDoc
