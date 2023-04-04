-- Why is it needed here, but not in "Universe.Core"?
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PatternSynonyms    #-}

module PlutusCore
    (
      -- * Parser
      parseProgram
    , parseTerm
    , parseType
    , SourcePos
    , SrcSpan (..)
    , SrcSpans
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
    , termMapNames
    , programMapNames
    , UniOf
    , Type (..)
    , typeSubtypes
    , typeMapNames
    , Kind (..)
    , toPatFuncKind
    , fromPatFuncKind
    , argsFunKind
    , ParserError (..)
    , Version (..)
    , Program (..)
    , Name (..)
    , TyName (..)
    , Unique (..)
    , UniqueMap (..)
    , Normalized (..)
    , latestVersion
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
    , TyDeBruijn (..)
    , NamedDeBruijn (..)
    , NamedTyDeBruijn (..)
    , deBruijnTerm
    , unDeBruijnTerm
    -- * Processing
    , HasUniques
    , Rename (..)
    -- * Type checking
    , module TypeCheck
    , normalizeTypesIn
    , normalizeTypesInProgram
    , AsTypeError (..)
    , TypeError
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
    ) where


import PlutusCore.Annotation
import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.DeBruijn
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.Evaluation.Machine.Ck
import PlutusCore.Flat ()
import PlutusCore.Name
import PlutusCore.Normalize
import PlutusCore.Parser
import PlutusCore.Quote
import PlutusCore.Rename
import PlutusCore.Size
import PlutusCore.Subst
import PlutusCore.TypeCheck as TypeCheck

-- | Applies one program to another. Fails if the versions do not match
-- and tries to merge annotations.
applyProgram
    :: Semigroup a
    => Program tyname name uni fun a
    -> Program tyname name uni fun a
    -> Maybe (Program tyname name uni fun a)
applyProgram (Program a1 v1 t1) (Program a2 v2 t2) | v1 == v2
  = Just $ Program (a1 <> a2) v1 (Apply (termAnn t1 <> termAnn t2) t1 t2)
applyProgram _ _ = Nothing
