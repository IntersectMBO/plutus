module Language.PlutusCore
    (
      -- * Parser
      parse
    , parseST
    , parseTermST
    , parseTypeST
    , parseScoped
    , parseProgram
    , parseTerm
    , parseType
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
    , Size
    , Value
    , BuiltinName (..)
    , TypeBuiltin (..)
    , defaultVersion
    , allBuiltinNames
    -- * Lexer
    , AlexPosn (..)
    -- * Views
    , IterApp (..)
    , TermIterApp
    , PrimIterApp
    -- * Formatting
    , format
    , formatDoc
    -- * Processing
    , annotateProgram
    , annotateTerm
    , annotateType
    , RenameError (..)
    , TyNameWithKind (..)
    , NameWithType (..)
    , TypeState (..)
    , RenamedType
    , RenamedTerm
    -- * Normalization
    , check
    , checkProgram
    , checkTerm
    , NormalizationError
    , checkFile
    , isTypeValue
    , isTermValue
    -- * Type synthesis
    , typecheckProgram
    , typecheckTerm
    , kindCheck
    , fileType
    , fileNormalizeType
    , fileTypeCfg
    , printType
    , printNormalizeType
    , TypeError (..)
    , TypeCheckCfg (..)
    , TypeCheckM
    , parseTypecheck
    -- for testing
    , normalizeType
    , runTypeCheckM
    , typecheckPipeline
    , defaultTypecheckerGas
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
    -- * Quotation and term construction
    , Quote
    , runQuote
    , QuoteT
    , runQuoteT
    , MonadQuote
    , liftQuote
    , convertErrors
    -- * Name generation
    , freshUnique
    , freshName
    , freshTyName
    -- * Quasi-Quoters
    , plcType
    , plcTerm
    , plcProgram
    -- * Evaluation
    , EvaluationResult (..)
    -- * Combining programs
    , applyProgram
    ) where

import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.ByteString.Lazy                     as BSL
import qualified Data.Text                                as T
import           Data.Text.Prettyprint.Doc
import           Language.PlutusCore.CBOR
import           Language.PlutusCore.Error
import           Language.PlutusCore.Evaluation.CkMachine
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.TH
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeSynthesis
import           Language.PlutusCore.View
import           PlutusPrelude

-- | Given a file at @fibonacci.plc@, @fileType "fibonacci.plc"@ will display
-- its type or an error message.
fileType :: FilePath -> IO T.Text
fileType = fileNormalizeType False

fileNormalizeType :: Bool -> FilePath -> IO T.Text
fileNormalizeType norm = fmap (either prettyPlcDefText id . printNormalizeType norm) . BSL.readFile

-- | Given a file, display
-- its type or an error message, optionally dumping annotations and debug
-- information.
fileTypeCfg :: PrettyConfigPlc -> FilePath -> IO T.Text
fileTypeCfg cfg = fmap (either (prettyTextBy cfg) id . printType) . BSL.readFile

checkFile :: FilePath -> IO (Maybe T.Text)
checkFile = fmap (either (pure . prettyText) id . fmap (fmap prettyPlcDefText . check) . parse) . BSL.readFile

-- | Print the type of a program contained in a 'ByteString'
printType :: (MonadError (Error AlexPosn) m) => BSL.ByteString -> m T.Text
printType = printNormalizeType False

-- | Print the type of a program contained in a 'ByteString'
printNormalizeType :: (MonadError (Error AlexPosn) m) => Bool -> BSL.ByteString -> m T.Text
printNormalizeType norm bs = runQuoteT $ prettyPlcDefText <$>
    (typecheckProgram (TypeCheckCfg 1000 norm) <=< annotateProgram <=< (liftEither . convertError . parseScoped)) bs

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped :: (MonadError (Error AlexPosn) m) => BSL.ByteString -> m (Program TyName Name AlexPosn)
parseScoped str = liftEither $ convertError $ fmap (\(p, s) -> rename s p) $ runExcept $ runStateT (parseST str) emptyIdentifierState

-- | Parse a program and typecheck it.
parseTypecheck :: (MonadError (Error AlexPosn) m, MonadQuote m) => Natural -> BSL.ByteString -> m (NormalizedType TyNameWithKind ())
parseTypecheck gas = typecheckPipeline gas <=< parseProgram

-- | Typecheck a program.
typecheckPipeline :: (MonadError (Error a) m, MonadQuote m) => Natural -> Program TyName Name a -> m (NormalizedType TyNameWithKind ())
typecheckPipeline gas p = do
    checkProgram p
    typecheckProgram (TypeCheckCfg gas False) =<< annotateProgram p

formatDoc :: (MonadError (Error AlexPosn) m) => BSL.ByteString -> m (Doc a)
formatDoc bs = runQuoteT $ prettyPlcDef <$> parseProgram bs

format :: (MonadError (Error AlexPosn) m) => PrettyConfigPlc -> BSL.ByteString -> m T.Text
format cfg = fmap (prettyTextBy cfg) . parseScoped

-- | The default version of Plutus Core supported by this library.
defaultVersion :: a -> Version a
defaultVersion a = Version a 1 0 0

-- | The default amount of gas to run the typechecker with.
defaultTypecheckerGas :: Natural
defaultTypecheckerGas = 1000

-- | Take one PLC program and apply it to another.
applyProgram :: Program tyname name () -> Program tyname name () -> Program tyname name ()
-- TODO: some kind of version checking
applyProgram (Program _ _ t1) (Program _ _ t2) = Program () (defaultVersion ()) (Apply () t1 t2)
