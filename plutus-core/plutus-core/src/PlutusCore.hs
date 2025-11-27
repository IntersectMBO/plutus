-- Why is it needed here, but not in "Universe.Core"?
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PatternSynonyms #-}

module PlutusCore
  ( -- * Parser
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
  , Closed (..)
  , EverywhereAll
  , knownUniOf
  , GShow (..)
  , show
  , GEq (..)
  , HasUniApply (..)
  , checkStar
  , withApplicable
  , (:~:) (..)
  , type (<:)
  , HasTypeLevel
  , HasTermLevel
  , HasTypeAndTermLevel
  , DefaultUni (..)
  , pattern DefaultUniList
  , pattern DefaultUniPair
  , pattern DefaultUniArray
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
  , UniqueSet (..)
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
  , TypeError

    -- * Errors
  , Error (..)
  , NormCheckError (..)
  , UniqueError (..)
  , FreeVariableError (..)

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
  , termAstSize
  , typeAstSize
  , kindAstSize
  , programAstSize
  ) where

import PlutusCore.Annotation
import PlutusCore.AstSize
import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.DeBruijn
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.Evaluation.Machine.Ck
import PlutusCore.FlatInstances ()
import PlutusCore.Name.Unique
import PlutusCore.Name.UniqueMap
import PlutusCore.Name.UniqueSet
import PlutusCore.Normalize
import PlutusCore.Parser
import PlutusCore.Quote
import PlutusCore.Rename
import PlutusCore.Subst
import PlutusCore.TypeCheck as TypeCheck

import Control.Monad.Except

{-| Applies one program to another. Fails if the versions do not match
and tries to merge annotations. -}
applyProgram
  :: (MonadError ApplyProgramError m, Semigroup a)
  => Program tyname name uni fun a
  -> Program tyname name uni fun a
  -> m (Program tyname name uni fun a)
applyProgram (Program a1 v1 t1) (Program a2 v2 t2)
  | v1 == v2 =
      pure $ Program (a1 <> a2) v1 (Apply (termAnn t1 <> termAnn t2) t1 t2)
applyProgram (Program _a1 v1 _t1) (Program _a2 v2 _t2) =
  throwError $ MkApplyProgramError v1 v2
