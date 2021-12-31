-- Why is it needed here, but not in "Universe.Core"?
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}

module PlutusCore
    (
      -- * Parser
      parseProgram
    , parseTerm
    , parseType
    , parseScoped
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
    , SourcePos
    -- * Formatting
    , format
    , formatDoc
    -- * Processing
    , HasUniques
    , Rename (..)
    -- * Type checking
    , module TypeCheck
    -- , fileType
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
import Text.Megaparsec (SourcePos, errorBundlePretty, initialPos)

topSourcePos :: SourcePos
topSourcePos = initialPos "top"

-- -- | Given a file at @fibonacci.plc@, @fileType "fibonacci.plc"@ will display
-- -- its type or an error message.
-- fileType :: FilePath -> IO T.Text
-- fileType file = do
--     bs <- BSL.readFile file
--     ty <- printType bs
--     pure $ T.pack $ show ty

-- | Print the type of a program contained in a 'ByteString'
-- printType
--     :: BSL.ByteString
--     -> Either (ParseErrorBundle T.Text ParseError) T.Text
-- printType :: (AsTypeError
--    err
--    (Term TyName Name DefaultUni DefaultFun ())
--    DefaultUni
--    DefaultFun
--    SourcePos,
--  MonadQuote f, MonadError err f) =>
    -- BSL.ByteString -> f (Normalized (Type TyName DefaultUni ()))
printType :: (AsTypeError
   err
   (Term TyName Name DefaultUni DefaultFun ())
   DefaultUni
   DefaultFun
   SourcePos,
 MonadQuote f, MonadError err f) =>
 BSL.ByteString -> f T.Text
printType bs = do
    case runQuoteT $ parseScoped bs of
      Left peb -> pure $ error $ "errorBundlePretty peb"
      Right pro -> do
        config <- getDefTypeCheckConfig topSourcePos
        ty <- inferTypeOfProgram config pro
        pure $ pack $ show $ pretty ty


-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
-- parseScoped
--     :: BSL.ByteString
--     -> Either (ParseErrorBundle T.Text ParseError) (Program TyName Name DefaultUni DefaultFun SourcePos)
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped :: (MonadQuote f) =>
    BSL.ByteString
    -> f (Program TyName Name DefaultUni DefaultFun SourcePos)
parseScoped bs = do
    -- case parseProgram bs of
    --   Left peb -> pure $ error $ errorBundlePretty peb
    --   Right pro -> do
    --     renamed <- rename pro
    --     through (Uniques.checkProgram (const True)) renamed
    case parseProgram bs of
        -- when fail, pretty print the parse errors.
        Left err ->
            errorWithoutStackTrace $ errorBundlePretty err
        -- otherwise,
        Right p -> do
            -- run @rename@ through the program
            renamed <- runQuoteT $ rename p
            -- check the program for @UniqueError@'s
            let checked = through (Uniques.checkProgram (const True)) renamed
            case checked of
                -- pretty print the error
                Left (err :: UniqueError SourcePos) ->
                    errorWithoutStackTrace $ render $ pretty err
                -- if there's no errors, return the parsed program
                Right _ -> pure p


-- | Parse a program and typecheck it.
-- parseTypecheck
--     :: TypeCheckConfig DefaultUni DefaultFun
--     -> BSL.ByteString
--     -> Either (ParseErrorBundle T.Text ParseError) (Normalized (Type TyName DefaultUni ()))
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

-- formatDoc ::
--     PrettyConfigPlc -> BSL.ByteString ->
--         Either (ParseErrorBundle T.Text ParseError) (Doc a)
-- don't use parseScoped since we don't bother running sanity checks when we format
-- formatDoc :: config -> a -> Program TyName Name DefaultUni DefaultFun (Doc ann)
formatDoc cfg bs = do
    case parseProgram bs of
        -- when fail, pretty print the parse errors.
        Left err ->
            errorWithoutStackTrace $ errorBundlePretty err
        -- otherwise,
        Right p -> do
            -- run @rename@ through the program
            renamed <- runQuoteT $ rename p
            fmap (prettyBy cfg) . rename renamed

format cfg bs = do
    case parseProgram bs of
        -- when fail, pretty print the parse errors.
        Left err ->
            errorWithoutStackTrace $ errorBundlePretty err
        -- otherwise,
        Right p -> do
            -- run @rename@ through the program
            renamed <- runQuoteT $ rename p
            fmap (displayBy cfg) . rename renamed


-- | Take one PLC program and apply it to another.
applyProgram
    :: Monoid a
    => Program tyname name uni fun a
    -> Program tyname name uni fun a
    -> Program tyname name uni fun a
applyProgram (Program a1 _ t1) (Program a2 _ t2) = Program (a1 <> a2) (defaultVersion mempty) (Apply mempty t1 t2)
