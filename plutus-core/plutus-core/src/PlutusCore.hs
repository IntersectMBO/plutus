-- Why is it needed here, but not in "Universe.Core"?
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE PatternSynonyms    #-}

module PlutusCore
    (
      -- * Parser
      parseProgram
    , parseTerm
    , parseType
    , parseScoped
    , topSourcePos
    , bsToText
    -- * Builtins
    , Some (..)
    , SomeTypeIn (..)
    , Kinded (..)
    , ValueOf (..)
    , someValueOf
    , someValue
    , someValueType
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
    , ParserError (..)
    , Version (..)
    , Program (..)
    , Name (..)
    , TyName (..)
    , Unique (..)
    , UniqueMap (..)
    , Normalized (..)
    , defaultVersion
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
    -- * Processing
    , HasUniques
    , Rename (..)
    -- * Type checking
    , module TypeCheck
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
import Data.Text.Lazy (toStrict)
import Data.Text.Lazy.Encoding (decodeUtf8')
import PlutusCore.Parser (parseProgram, parseTerm, parseType)
import Text.Megaparsec (SourcePos, initialPos)

topSourcePos :: SourcePos
topSourcePos = initialPos "top"

printType ::(AsParserErrorBundle e, AsUniqueError e SourcePos, AsTypeError e (Term TyName Name DefaultUni DefaultFun ()) DefaultUni DefaultFun SourcePos,
        MonadError e m)
    => BSL.ByteString
    -> m T.Text
printType bs = runQuoteT $ T.pack . show . pretty <$> do
    scoped <- parseScoped $ bsToText bs
    config <- getDefTypeCheckConfig topSourcePos
    inferTypeOfProgram config scoped

bsToText :: BSL.ByteString -> T.Text
bsToText bs = toStrict $
    case decodeUtf8' bs of
        Left err  -> error $ "bsToText: Decoding from bytestring to text failed with unicode exception: " <> show err
        Right txt -> txt

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped :: (AsParserErrorBundle e, AsUniqueError e SourcePos,
        MonadError e m, MonadQuote m) =>
    T.Text
    -> m (Program TyName Name DefaultUni DefaultFun SourcePos)
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped = through (Uniques.checkProgram (const True)) <=< rename <=< parseProgram

-- | Parse a program and typecheck it.
parseTypecheck :: ( AsParserErrorBundle e, AsUniqueError e SourcePos,
   AsTypeError
   e
   (Term TyName Name DefaultUni DefaultFun ())
   DefaultUni
   DefaultFun
   SourcePos,
 MonadError e m, MonadQuote m) =>
    TypeCheckConfig DefaultUni DefaultFun
    -> BSL.ByteString -> m (Normalized (Type TyName DefaultUni ()))
parseTypecheck cfg = typecheckPipeline cfg <=< parseScoped . bsToText

-- | Typecheck a program.
typecheckPipeline
    :: (AsTypeError e (Term TyName Name DefaultUni DefaultFun ()) DefaultUni DefaultFun a,
        MonadError e m,
        MonadQuote m)
    => TypeCheckConfig DefaultUni DefaultFun
    -> Program TyName Name DefaultUni DefaultFun a
    -> m (Normalized (Type TyName DefaultUni ()))
typecheckPipeline = inferTypeOfProgram
format
    :: (AsParserErrorBundle e, MonadError e m)
    => PrettyConfigPlc -> BSL.ByteString -> m T.Text
format cfg = runQuoteT . fmap (displayBy cfg) . (rename <=< parseProgram . bsToText)

-- | Take one PLC program and apply it to another.
applyProgram
    :: Monoid a
    => Program tyname name uni fun a
    -> Program tyname name uni fun a
    -> Program tyname name uni fun a
applyProgram (Program a1 _ t1) (Program a2 _ t2) = Program (a1 <> a2) (defaultVersion mempty) (Apply mempty t1 t2)
