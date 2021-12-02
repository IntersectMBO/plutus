-- Why is it needed here, but not in "Universe.Core"?
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PatternSynonyms    #-}

module PlutusCore
    (
      -- * Parser
      parseProgram
    , parseTerm
    , parseType
    , parseScoped
    , topAlexPosn
    -- * Builtins
    , Some (..)
    , SomeTypeIn (..)
    , Kinded (..)
    , ValueOf (..)
    , someValueOf
    , someValue
    , Esc
    , Contains (..)
    , Includes
    , Closed (..)
    , EverywhereAll
    , knownUniOf
    , GShow (..)
    , show
    , GEq (..)
    , deriveGEq
    , HasUniApply (..)
    , checkStar
    , withApplicable
    , (:~:) (..)
    , type (<:)
    , DefaultUni (..)
    , pattern DefaultUniList
    , pattern DefaultUniPair
    , DefaultFun (..)
    -- * AST
    , Term (..)
    , termSubterms
    , termSubtypes
    , UniOf
    , Type (..)
    , typeSubtypes
    , Kind (..)
    , ParseError (..)
    , Version (..)
    , Program (..)
    , Name (..)
    , TyName (..)
    , Unique (..)
    , UniqueMap (..)
    , Normalized (..)
    , defaultVersion
    , toTerm
    , termAnn
    , typeAnn
    , tyVarDeclAnn
    , tyVarDeclName
    , tyVarDeclKind
    , varDeclAnn
    , varDeclName
    , varDeclType
    , tyDeclAnn
    , tyDeclType
    , tyDeclKind
    , progAnn
    , progVer
    , progTerm
    , mapFun
    -- * DeBruijn representation
    , DeBruijn (..)
    , NamedDeBruijn (..)
    , deBruijnTerm
    , unDeBruijnTerm
    -- * Lexer
    , AlexPosn (..)
    -- * Formatting
    , format
    , formatDoc
    -- * Processing
    , HasUniques
    , Rename (..)
    -- * Type checking
    , module TypeCheck
    , fileType
    , fileTypeCfg
    , printType
    , normalizeTypesIn
    , normalizeTypesInProgram
    , AsTypeError (..)
    , TypeError
    , parseTypecheck
    -- for testing
    , typecheckPipeline
    -- * Errors
    , Error (..)
    , AsError (..)
    , NormCheckError (..)
    , AsNormCheckError (..)
    , UniqueError (..)
    , AsUniqueError (..)
    , FreeVariableError (..)
    , AsFreeVariableError (..)
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
    -- * Combining programs
    , applyProgram
    -- * Benchmarking
    , termSize
    , typeSize
    , kindSize
    , programSize
    , serialisedSize
    -- * Budgeting defaults
    , defaultBuiltinCostModel
    , defaultBuiltinsRuntime
    , defaultCekCostModel
    , defaultCekMachineCosts
    , defaultCekParameters
    , defaultCostModelParams
    , unitCekParameters
    -- * CEK machine costs
    , cekMachineCostsPrefix
    , CekMachineCosts (..)
    ) where

import PlutusPrelude

import PlutusCore.Check.Uniques qualified as Uniques
import PlutusCore.Core
import PlutusCore.DeBruijn
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.Evaluation.Machine.Ck
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Flat ()
import PlutusCore.Name
import PlutusCore.Normalize
import PlutusCore.Pretty
import PlutusCore.Quote
import PlutusCore.Rename
import PlutusCore.Size
import PlutusCore.TypeCheck as TypeCheck

import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts

import Control.Monad.Except
import Data.ByteString.Lazy qualified as BSL
import Data.Text qualified as T

-- | Given a file at @fibonacci.plc@, @fileType "fibonacci.plc"@ will display
-- its type or an error message.
fileType :: FilePath -> IO T.Text
fileType = fmap (either prettyErr id . printType) . BSL.readFile
    where
        prettyErr :: Error DefaultUni DefaultFun AlexPosn -> T.Text
        prettyErr = displayPlcDef

-- | Given a file, display
-- its type or an error message, optionally dumping annotations and debug
-- information.
fileTypeCfg :: PrettyConfigPlc -> FilePath -> IO T.Text
fileTypeCfg cfg = fmap (either prettyErr id . printType) . BSL.readFile
    where
        prettyErr :: Error DefaultUni DefaultFun AlexPosn -> T.Text
        prettyErr = displayBy cfg

-- | Print the type of a program contained in a 'ByteString'
printType
    :: (AsParseError e AlexPosn,
        AsUniqueError e AlexPosn,
        AsTypeError e (Term TyName Name DefaultUni DefaultFun ()) DefaultUni DefaultFun AlexPosn,
        MonadError e m)
    => BSL.ByteString
    -> m T.Text
printType bs = runQuoteT $ T.pack . show . pretty <$> do
    scoped <- parseScoped bs
    config <- getDefTypeCheckConfig topAlexPosn
    inferTypeOfProgram config scoped

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped
    :: (AsParseError e AlexPosn,
        AsUniqueError e AlexPosn,
        MonadError e m,
        MonadQuote m)
    => BSL.ByteString
    -> m (Program TyName Name DefaultUni DefaultFun AlexPosn)
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped = through (Uniques.checkProgram (const True)) <=< rename <=< parseProgram

-- | Parse a program and typecheck it.
parseTypecheck
    :: (AsParseError e AlexPosn,
        AsUniqueError e AlexPosn,
        AsTypeError e (Term TyName Name DefaultUni DefaultFun ()) DefaultUni DefaultFun AlexPosn,
        MonadError e m,
        MonadQuote m)
    => TypeCheckConfig DefaultUni DefaultFun
    -> BSL.ByteString
    -> m (Normalized (Type TyName DefaultUni ()))
parseTypecheck cfg = typecheckPipeline cfg <=< parseScoped

-- | Typecheck a program.
typecheckPipeline
    :: (AsTypeError e (Term TyName Name DefaultUni DefaultFun ()) DefaultUni DefaultFun a,
        MonadError e m,
        MonadQuote m)
    => TypeCheckConfig DefaultUni DefaultFun
    -> Program TyName Name DefaultUni DefaultFun a
    -> m (Normalized (Type TyName DefaultUni ()))
typecheckPipeline = inferTypeOfProgram

parseProgramDef
    :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m)
    => BSL.ByteString -> m (Program TyName Name DefaultUni DefaultFun AlexPosn)
parseProgramDef = parseProgram

formatDoc :: (AsParseError e AlexPosn, MonadError e m) => PrettyConfigPlc -> BSL.ByteString -> m (Doc a)
-- don't use parseScoped since we don't bother running sanity checks when we format
formatDoc cfg = runQuoteT . fmap (prettyBy cfg) . (rename <=< parseProgramDef)

format
    :: (AsParseError e AlexPosn, MonadError e m)
    => PrettyConfigPlc -> BSL.ByteString -> m T.Text
-- don't use parseScoped since we don't bother running sanity checks when we format
format cfg = runQuoteT . fmap (displayBy cfg) . (rename <=< parseProgramDef)

-- | Take one PLC program and apply it to another.
applyProgram
    :: Monoid a
    => Program tyname name uni fun a
    -> Program tyname name uni fun a
    -> Program tyname name uni fun a
applyProgram (Program a1 _ t1) (Program a2 _ t2) = Program (a1 <> a2) (defaultVersion mempty) (Apply mempty t1 t2)
