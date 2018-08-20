module Language.PlutusCore
    ( Configuration (..)
    , defaultCfg
    , debugCfg
      -- * Parser
    , parse
    , parseScoped
    -- * Pretty-printing
    , prettyText
    , debugText
    , prettyString
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
    , RenameError (..)
    , TyNameWithKind (..)
    , NameWithType (..)
    , Debug (..)
    , TypeState (..)
    , RenamedType
    , RenamedTerm
    -- * Normalization
    , check
    , NormalizationError
    -- * Type synthesis
    , typeOf
    , kindOf
    , runTypeCheckM
    , programType
    , fileType
    , printType
    , TypeError (..)
    , TypeCheckM
    , BuiltinTable (..)
    -- * Serialization
    , encodeProgram
    , decodeProgram
    , readProgram
    , writeProgram
    -- * Errors
    , Error (..)
    , IsError (..)
    -- * Base functors
    , TermF (..)
    , TypeF (..)
    , Fresh
    , dropFresh
    ) where

import qualified Data.ByteString.Lazy              as BSL
import qualified Data.IntMap                       as IM
import qualified Data.Text                         as T
import           Data.Text.Prettyprint.Doc         hiding (annotate)
import           Language.PlutusCore.CBOR
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

-- TODO: optionally print annotations
newtype Configuration = Configuration Bool

-- | Given a file at @fibonacci.plc@, @fileType "fibonacci.plc"@ will display
-- its type or an error message.
fileType :: FilePath -> IO T.Text
fileType = fmap (either prettyText id . printType) . BSL.readFile

-- | Print the type of a program contained in a 'ByteString'
printType :: BSL.ByteString -> Either Error T.Text
printType = collectErrors . fmap (convertError . typeErr <=< convertError . annotateST) . parseScoped

typeErr :: (TypeState a, Program TyNameWithKind NameWithType a) -> Either (TypeError a) T.Text
typeErr = fmap prettyText . uncurry (programType 10000)

-- | This is the default 'Configuration' most users will want
defaultCfg :: Configuration
defaultCfg = Configuration False

-- | Use this 'Configuration' when debugging the library
debugCfg :: Configuration
debugCfg = Configuration True

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

format :: Configuration -> BSL.ByteString -> Either ParseError T.Text
format (Configuration True)  = fmap (render . debug) . parseScoped
format (Configuration False) = fmap render . formatDoc
