module Language.PlutusCore
    ( -- * Parser
      parse
    , parseScoped
    -- * Pretty-printing
    , prettyText
    -- * AST
    , Term (..)
    , Type (..)
    , Constant (..)
    , Kind (..)
    , ParseError (..)
    , Version (..)
    , Program (..)
    , Name (..)
    , TyName (..)
    , Unique (..)
    , BuiltinName (..)
    , TypeBuiltin (..)
    -- * Lexer
    , AlexPosn (..)
    -- * Formatting
    , format
    , formatDoc
    -- * Processing
    , annotate
    , annotateST
    , debugScopes
    , RenamedTerm
    , RenamedType
    , RenameError (..)
    , TyNameWithKind (..)
    , NameWithType (..)
    , Debug (..)
    , TypeState (..)
    -- * Normalization
    , normalize
    -- * Type synthesis
    , typeOf
    , kindOf
    , runTypeCheckM
    , TypeError (..)
    -- * Errors
    , Error (..)
    , IsError (..)
    -- * Base functors
    , TermF (..)
    , TypeF (..)
    ) where

import qualified Data.ByteString.Lazy                  as BSL
import qualified Data.Text                             as T
import           Data.Text.Prettyprint.Doc             hiding (annotate)
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeSynthesis

debugScopes :: BSL.ByteString -> Either ParseError T.Text
debugScopes = fmap (render . debug) . parseScoped

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped :: BSL.ByteString -> Either ParseError (Program TyName Name AlexPosn)
parseScoped = fmap (uncurry rename) . parseST

formatDoc :: BSL.ByteString -> Either ParseError (Doc a)
formatDoc = fmap pretty . parse

-- | Render a 'Program' as strict 'Text'.
prettyText :: Program TyName Name a -> T.Text
prettyText = render . pretty

render :: Doc a -> T.Text
render = renderStrict . layoutSmart defaultLayoutOptions

format :: BSL.ByteString -> Either ParseError T.Text
format = fmap render . formatDoc
