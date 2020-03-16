-- Why is it needed here, but not in 'Universe.hs'?
{-# LANGUAGE ExplicitNamespaces #-}

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
    -- * Universe
    , Some (..)
    , TypeIn (..)
    , ValueOf (..)
    , someValue
    , Includes (..)
    , Closed (..)
    , knownUniOf
    , GShow (..)
    , show
    , GEq (..)
    , deriveGEq
    , (:~:) (..)
    , Lift
    , GLift (..)
    , type (<:)
    , DefaultUni (..)
    -- * AST
    , Term (..)
    , termSubterms
    , termSubtypes
    , Type (..)
    , typeSubtypes
    , Builtin (..)
    , Kind (..)
    , ParseError (..)
    , Version (..)
    , Program (..)
    , Name (..)
    , TyName (..)
    , Unique (..)
    , UniqueMap (..)
    , Value
    , BuiltinName (..)
    , DynamicBuiltinName (..)
    , StagedBuiltinName (..)
    , Normalized (..)
    , defaultVersion
    , allBuiltinNames
    , allKeywords
    , toTerm
    , termAnn
    , typeAnn
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
    , HasUniques
    , Rename (..)
    -- * Type checking
    , module TypeCheck
    , fileType
    , fileNormalizeType
    , fileTypeCfg
    , printType
    , printNormalizeType
    , normalizeTypesIn
    , normalizeTypesInProgram
    , InternalTypeError (..)
    , TypeError (..)
    , AsTypeError (..)
    , parseTypecheck
    -- for testing
    , typecheckPipeline
    -- * Errors
    , Error (..)
    , AsError (..)
    , AsNormCheckError (..)
    , UnknownDynamicBuiltinNameError (..)
    , UniqueError (..)
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
    -- * Evaluation
    , EvaluationResult (..)
    , EvaluationResultDef
    -- * Combining programs
    , applyProgram
    -- * Benchmarking
    , termSize
    , typeSize
    , kindSize
    , programSize
    , serialisedSize
    ) where

import           PlutusPrelude

import           Language.PlutusCore.CBOR                  ()
import qualified Language.PlutusCore.Check.Normal          as Normal
import qualified Language.PlutusCore.Check.Uniques         as Uniques
import           Language.PlutusCore.Core
import           Language.PlutusCore.Error
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename
import           Language.PlutusCore.Size
import           Language.PlutusCore.TypeCheck             as TypeCheck
import           Language.PlutusCore.Universe
import           Language.PlutusCore.View

import           Control.Monad.Except
import qualified Data.ByteString.Lazy                      as BSL
import qualified Data.Text                                 as T

-- | Given a file at @fibonacci.plc@, @fileType "fibonacci.plc"@ will display
-- its type or an error message.
fileType :: FilePath -> IO T.Text
fileType = fileNormalizeType False

fileNormalizeType :: Bool -> FilePath -> IO T.Text
fileNormalizeType norm = fmap (either prettyErr id . printNormalizeType norm) . BSL.readFile
    where
        prettyErr :: Error DefaultUni AlexPosn -> T.Text
        prettyErr = prettyPlcDefText

-- | Given a file, display
-- its type or an error message, optionally dumping annotations and debug
-- information.
fileTypeCfg :: PrettyConfigPlc -> FilePath -> IO T.Text
fileTypeCfg cfg = fmap (either prettyErr id . printType) . BSL.readFile
    where
        prettyErr :: Error DefaultUni AlexPosn -> T.Text
        prettyErr = prettyTextBy cfg

-- | Print the type of a program contained in a 'ByteString'
printType
    :: (AsParseError e AlexPosn,
        AsUniqueError e AlexPosn,
        AsTypeError e DefaultUni AlexPosn,
        MonadError e m)
    => BSL.ByteString
    -> m T.Text
printType = printNormalizeType False

-- | Print the type of a program contained in a 'ByteString'
printNormalizeType
    :: (AsParseError e AlexPosn,
        AsUniqueError e AlexPosn,
        AsTypeError e DefaultUni AlexPosn,
        MonadError e m)
    => Bool
    -> BSL.ByteString
    -> m T.Text
printNormalizeType norm bs = runQuoteT $ prettyPlcDefText <$> do
    scoped <- parseScoped bs
    inferTypeOfProgram (TypeCheckConfig norm mempty) scoped

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped
    :: (AsParseError e AlexPosn,
        AsUniqueError e AlexPosn,
        MonadError e m,
        MonadQuote m)
    => BSL.ByteString
    -> m (Program TyName Name DefaultUni AlexPosn)
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped = through (Uniques.checkProgram (const True)) <=< rename <=< parseProgram

-- | Parse a program and typecheck it.
parseTypecheck
    :: (AsParseError e AlexPosn,
        AsUniqueError e AlexPosn,
        AsNormCheckError e TyName Name DefaultUni AlexPosn,
        AsTypeError e DefaultUni AlexPosn,
        MonadError e m,
        MonadQuote m)
    => TypeCheckConfig DefaultUni -> BSL.ByteString -> m (Normalized (Type TyName DefaultUni ()))
parseTypecheck cfg = typecheckPipeline cfg <=< parseScoped

-- | Typecheck a program.
typecheckPipeline
    :: (AsNormCheckError e TyName Name DefaultUni a,
        AsTypeError e DefaultUni a,
        MonadError e m,
        MonadQuote m)
    => TypeCheckConfig DefaultUni
    -> Program TyName Name DefaultUni a
    -> m (Normalized (Type TyName DefaultUni ()))
typecheckPipeline cfg =
    inferTypeOfProgram cfg
    <=< through (unless (_tccDoNormTypes cfg) . Normal.checkProgram)

parseProgramDef
    :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m)
    => BSL.ByteString -> m (Program TyName Name DefaultUni AlexPosn)
parseProgramDef = parseProgram

formatDoc :: (AsParseError e AlexPosn, MonadError e m) => PrettyConfigPlc -> BSL.ByteString -> m (Doc a)
-- don't use parseScoped since we don't bother running sanity checks when we format
formatDoc cfg = runQuoteT . fmap (prettyBy cfg) . (rename <=< parseProgramDef)

format
    :: (AsParseError e AlexPosn, MonadError e m)
    => PrettyConfigPlc -> BSL.ByteString -> m T.Text
-- don't use parseScoped since we don't bother running sanity checks when we format
format cfg = runQuoteT . fmap (prettyTextBy cfg) . (rename <=< parseProgramDef)

-- | Take one PLC program and apply it to another.
applyProgram :: Program tyname name uni () -> Program tyname name uni () -> Program tyname name uni ()
-- TODO: some kind of version checking
applyProgram (Program _ _ t1) (Program _ _ t2) = Program () (defaultVersion ()) (Apply () t1 t2)
