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
    , Builtin (..)
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
    , DynamicBuiltinName (..)
    , StagedBuiltinName (..)
    , TypeBuiltin (..)
    , Normalized (..)
    , NormalizedType
    , getNormalizedType
    , defaultVersion
    , allBuiltinNames
    , termLoc
    , tyLoc
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
    , AsRenameError (..)
    , TyNameWithKind (..)
    , NameWithType (..)
    , TypeState (..)
    , RenamedType
    , RenamedTerm
    , rename
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
    , dynamicBuiltinNameMeaningsToTypes
    , fileType
    , fileNormalizeType
    , fileTypeCfg
    , printType
    , printNormalizeType
    , InternalTypeError (..)
    , TypeError (..)
    , AsTypeError (..)
    , TypeConfig (..)
    , DynamicBuiltinNameTypes (..)
    , TypeCheckM
    , parseTypecheck
    -- for testing
    , normalizeType
    , runTypeCheckM
    , typecheckPipeline
    , defaultTypecheckerGas
    -- * Errors
    , Error (..)
    , AsError (..)
    , UnknownDynamicBuiltinNameError (..)
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
    -- * Name generation
    , freshUnique
    , freshName
    , freshTyName
    -- * Quasi-Quoters
    , plcType
    , plcTerm
    , plcProgram
    -- * Evaluation
    , EvaluationResultF (EvaluationSuccess, EvaluationFailure)
    , EvaluationResult
    -- * Combining programs
    , applyProgram
    ) where

import           Control.Monad.Except
import qualified Data.ByteString.Lazy                     as BSL
import qualified Data.Text                                as T
import           Data.Text.Prettyprint.Doc
import           Language.PlutusCore.CBOR                 ()
import           Language.PlutusCore.Check.Normal
import           Language.PlutusCore.Error
import           Language.PlutusCore.Evaluation.CkMachine
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
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
fileNormalizeType norm = fmap (either prettyErr id . printNormalizeType norm) . BSL.readFile
    where
        prettyErr :: Error AlexPosn -> T.Text
        prettyErr = prettyPlcDefText

-- | Given a file, display
-- its type or an error message, optionally dumping annotations and debug
-- information.
fileTypeCfg :: PrettyConfigPlc -> FilePath -> IO T.Text
fileTypeCfg cfg = fmap (either prettyErr id . printType) . BSL.readFile
    where
        prettyErr :: Error AlexPosn -> T.Text
        prettyErr = prettyTextBy cfg

checkFile :: FilePath -> IO (Maybe T.Text)
checkFile = fmap (either (pure . prettyText) id . fmap (fmap prettyPlcDefText . check) . parse) . BSL.readFile

-- | Print the type of a program contained in a 'ByteString'
printType :: (AsParseError e AlexPosn, AsRenameError e AlexPosn, AsTypeError e AlexPosn, MonadError e m) => BSL.ByteString -> m T.Text
printType = printNormalizeType False

-- | Print the type of a program contained in a 'ByteString'
printNormalizeType :: (AsParseError e AlexPosn, AsRenameError e AlexPosn, AsTypeError e AlexPosn, MonadError e m) => Bool -> BSL.ByteString -> m T.Text
printNormalizeType norm bs = runQuoteT $ prettyPlcDefText <$> do
    scoped <- parseScoped bs
    annotated <- annotateProgram scoped
    typecheckProgram (TypeConfig norm mempty (Just 1000)) annotated

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped :: (AsParseError e AlexPosn, MonadError e m) => BSL.ByteString -> m (Program TyName Name AlexPosn)
parseScoped str = runQuoteT $ parseProgram str >>= rename

-- | Parse a program and typecheck it.
parseTypecheck
    :: (AsParseError e AlexPosn,
        AsNormalizationError e TyName Name AlexPosn,
        AsRenameError e AlexPosn,
        AsTypeError e AlexPosn,
        MonadError e m,
        MonadQuote m)
    => Maybe Natural -> BSL.ByteString -> m (NormalizedType TyNameWithKind ())
parseTypecheck gas = typecheckPipeline gas <=< parseScoped

-- | Typecheck a program.
typecheckPipeline :: (AsNormalizationError e TyName Name a, AsRenameError e a, AsTypeError e a, MonadError e m, MonadQuote m) => Maybe Natural -> Program TyName Name a -> m (NormalizedType TyNameWithKind ())
typecheckPipeline gas p = do
    checkProgram p
    typecheckProgram (TypeConfig False mempty gas) =<< annotateProgram p

formatDoc :: (AsParseError e AlexPosn, MonadError e m) => BSL.ByteString -> m (Doc a)
formatDoc bs = runQuoteT $ prettyPlcDef <$> parseProgram bs

format :: (AsParseError e AlexPosn, MonadError e m) => PrettyConfigPlc -> BSL.ByteString -> m T.Text
format cfg = fmap (prettyTextBy cfg) . parseScoped

-- | The default version of Plutus Core supported by this library.
defaultVersion :: a -> Version a
defaultVersion a = Version a 1 0 0

-- | The default amount of gas to run the typechecker with.
defaultTypecheckerGas :: Maybe Natural
defaultTypecheckerGas = Just 1000

-- | Take one PLC program and apply it to another.
applyProgram :: Program tyname name () -> Program tyname name () -> Program tyname name ()
-- TODO: some kind of version checking
applyProgram (Program _ _ t1) (Program _ _ t2) = Program () (defaultVersion ()) (Apply () t1 t2)
