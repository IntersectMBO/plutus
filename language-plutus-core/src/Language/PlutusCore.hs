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
    , programType
    , TypeError (..)
    -- * Errors
    , Error (..)
    , IsError (..)
    -- * Base functors
    , TermF (..)
    , TypeF (..)
    ) where

import qualified Data.ByteString.Lazy              as BSL
import qualified Data.IntMap                       as IM
import qualified Data.Text                         as T
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeSynthesis
import           PlutusPrelude

debugScopes :: BSL.ByteString -> Either ParseError T.Text
debugScopes = fmap (render . debug) . parseScoped

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped :: BSL.ByteString -> Either ParseError (Program TyName Name AlexPosn)
parseScoped = fmap (uncurry rename) . parseST

programType :: Natural -- ^ Gas provided to typechecker
            -> TypeState a
            -> Program TyNameWithKind NameWithType a
            -> Either (TypeError a) (RenamedType ())
programType n (TypeState _ tys) (Program _ _ t) = runTypeCheckM i n $ typeOf t
    where i = maybe 0 fst (IM.lookupMax tys)

formatDoc :: BSL.ByteString -> Either ParseError (Doc a)
formatDoc = fmap pretty . parse

format :: BSL.ByteString -> Either ParseError T.Text
format = fmap render . formatDoc
