{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module PlutusCore.Error
    ( ParseError (..)
    , AsParseError (..)
    , NormCheckError (..)
    , AsNormCheckError (..)
    , UniqueError (..)
    , AsUniqueError (..)
    , TypeError (..)
    , AsTypeError (..)
    , FreeVariableError (..)
    , AsFreeVariableError (..)
    , Error (..)
    , AsError (..)
    , throwingEither
    ) where

import PlutusPrelude

import PlutusCore.Core
import PlutusCore.DeBruijn.Internal
import PlutusCore.Name
import PlutusCore.Pretty

import Control.Lens hiding (use)
import Control.Monad.Error.Lens
import Control.Monad.Except
import Data.Text qualified as T
import ErrorCode
import Prettyprinter (hardline, indent, squotes, (<+>))
import Prettyprinter.Internal (Doc (Text))
import Text.Megaparsec.Error (ShowErrorComponent, showErrorComponent)
import Text.Megaparsec.Pos (SourcePos, sourcePosPretty)
import Universe (Closed (Everywhere), GEq, GShow)

-- | Lifts an 'Either' into an error context where we can embed the 'Left' value into the error.
throwingEither :: MonadError e m => AReview e t -> Either t a -> m a
throwingEither r e = case e of
    Left t  -> throwing r t
    Right v -> pure v

-- | An error encountered during parsing.
data ParseError
    = LexErr String
    | UnknownBuiltinType T.Text SourcePos
    | BuiltinTypeNotAStar T.Text SourcePos
    | UnknownBuiltinFunction T.Text SourcePos
    | InvalidBuiltinConstant T.Text T.Text SourcePos
    deriving (Eq, Ord, Generic, NFData)

makeClassyPrisms ''ParseError

instance Show ParseError
    where
      show = show . pretty

data UniqueError ann
    = MultiplyDefined Unique ann ann
    | IncoherentUsage Unique ann ann
    | FreeVariable Unique ann
    deriving (Show, Eq, Generic, NFData, Functor)
makeClassyPrisms ''UniqueError

data NormCheckError tyname name uni fun ann
    = BadType ann (Type tyname uni ann) T.Text
    | BadTerm ann (Term tyname name uni fun ann) T.Text
    deriving (Show, Functor, Generic, NFData)
deriving instance
    ( Eq (Term tyname name uni fun ann)
    , Eq (Type tyname uni ann)
    , GEq uni, Closed uni, uni `Everywhere` Eq
    , Eq fun, Eq ann
    ) => Eq (NormCheckError tyname name uni fun ann)
makeClassyPrisms ''NormCheckError

data TypeError term uni fun ann
    = KindMismatch ann (Type TyName uni ()) (Kind ()) (Kind ())
    | TypeMismatch ann
        term
        (Type TyName uni ())
        (Normalized (Type TyName uni ()))
    | FreeTypeVariableE ann TyName
    | FreeVariableE ann Name
    | UnknownBuiltinFunctionE ann fun
    deriving (Show, Eq, Generic, NFData, Functor)
makeClassyPrisms ''TypeError

data Error uni fun ann
    = ParseErrorE ParseError
    | UniqueCoherencyErrorE (UniqueError ann)
    | TypeErrorE (TypeError (Term TyName Name uni fun ()) uni fun ann)
    | NormCheckErrorE (NormCheckError TyName Name uni fun ann)
    | FreeVariableErrorE FreeVariableError
    deriving (Eq, Generic, NFData, Functor)
makeClassyPrisms ''Error
deriving instance (Show fun, Show ann, Closed uni, Everywhere uni Show, GShow uni, Show (ParseError ann)) => Show (Error uni fun ann)

instance AsParseError (Error uni fun ann) where
    _ParseError = _ParseErrorE

instance AsUniqueError (Error uni fun ann) ann where
    _UniqueError = _UniqueCoherencyErrorE

instance AsTypeError (Error uni fun ann) (Term TyName Name uni fun ()) uni fun ann where
    _TypeError = _TypeErrorE

instance (tyname ~ TyName, name ~ Name) =>
            AsNormCheckError (Error uni fun ann) tyname name uni fun ann where
    _NormCheckError = _NormCheckErrorE

instance AsFreeVariableError (Error uni fun ann) where
    _FreeVariableError = _FreeVariableErrorE

instance Pretty SourcePos where
    pretty = pretty . sourcePosPretty

instance Pretty ParseError where
    pretty (LexErr s)                       = "Lexical error:" <+> Text (length s) (T.pack s)
    pretty (UnknownBuiltinType s loc)       = "Unknown built-in type" <+> squotes (pretty s) <+> "at" <+> pretty loc
    pretty (BuiltinTypeNotAStar ty loc)     = "Expected a type of kind star (to later parse a constant), but got:" <+> squotes (pretty ty) <+> "at" <+> pretty loc
    pretty (UnknownBuiltinFunction s loc)   = "Unknown built-in function" <+> squotes (pretty s) <+> "at" <+> pretty loc
    pretty (InvalidBuiltinConstant c s loc) = "Invalid constant" <+> squotes (pretty c) <+> "of type" <+> squotes (pretty s) <+> "at" <+> pretty loc

instance ShowErrorComponent ParseError where
    showErrorComponent = show . pretty

instance Pretty ann => Show (ParseError ann)
    where
      show = show . pretty

instance Pretty ann => Pretty (UniqueError ann) where
    pretty (MultiplyDefined u def redef) =
        "Variable" <+> pretty u <+> "defined at" <+> pretty def <+>
        "is redefined at" <+> pretty redef
    pretty (IncoherentUsage u def use) =
        "Variable" <+> pretty u <+> "defined at" <+> pretty def <+>
        "is used in a different scope at" <+> pretty use
    pretty (FreeVariable u use) =
        "Variable" <+> pretty u <+> "is free at" <+> pretty use

instance ( Pretty ann
         , PrettyBy config (Type tyname uni ann)
         , PrettyBy config (Term tyname name uni fun ann)
         ) => PrettyBy config (NormCheckError tyname name uni fun ann) where
    prettyBy config (BadType ann ty expct) =
        "Malformed type at" <+> pretty ann <>
        ". Type" <+>  squotes (prettyBy config ty) <+>
        "is not a" <+> pretty expct <> "."
    prettyBy config (BadTerm ann t expct) =
        "Malformed term at" <+> pretty ann <>
        ". Term" <+> squotes (prettyBy config t) <+>
        "is not a" <+> pretty expct <> "."

instance (GShow uni, Closed uni, uni `Everywhere` PrettyConst,  Pretty ann, Pretty fun, Pretty term) =>
            PrettyBy PrettyConfigPlc (TypeError term uni fun ann) where
    prettyBy config e@(KindMismatch ann ty k k')          =
        pretty (errorCode e) <> ":" <+>
        "Kind mismatch at" <+> pretty ann <+>
        "in type" <+> squotes (prettyBy config ty) <>
        ". Expected kind" <+> squotes (prettyBy config k) <+>
        ", found kind" <+> squotes (prettyBy config k')
    prettyBy config (TypeMismatch ann t ty ty')         =
        "Type mismatch at" <+> pretty ann <>
        (if _pcpoCondensedErrors (_pcpOptions config) == CondensedErrorsYes
            then mempty
            -- TODO: we should use prettyBy here but the problem is
            -- that `instance PrettyClassic PIR.Term` whereas `instance PrettyPLC PLC.Term`
            else " in term" <> hardline <> indent 2 (squotes (pretty t)) <> ".") <>
        hardline <>
        "Expected type" <> hardline <> indent 2 (squotes (prettyBy config ty)) <>
        "," <> hardline <>
        "found type" <> hardline <> indent 2 (squotes (prettyBy config ty'))
    prettyBy config (FreeTypeVariableE ann name)          =
        "Free type variable at " <+> pretty ann <+> ": " <+> prettyBy config name
    prettyBy config (FreeVariableE ann name)              =
        "Free variable at " <+> pretty ann <+> ": " <+> prettyBy config name
    prettyBy _ (UnknownBuiltinFunctionE ann fun) =
        "An unknown built-in function at" <+> pretty ann <> ":" <+> pretty fun

instance (GShow uni, Closed uni, uni `Everywhere` PrettyConst, Pretty fun, Pretty ann) =>
            PrettyBy PrettyConfigPlc (Error uni fun ann) where
    prettyBy _      (ParseErrorE e)           = pretty e
    prettyBy _      (UniqueCoherencyErrorE e) = pretty e
    prettyBy config (TypeErrorE e)            = prettyBy config e
    prettyBy config (NormCheckErrorE e)       = prettyBy config e
    prettyBy _      (FreeVariableErrorE e)    = pretty e

instance HasErrorCode ParseError where
    errorCode InvalidBuiltinConstant {} = ErrorCode 10
    errorCode UnknownBuiltinFunction {} = ErrorCode 9
    errorCode UnknownBuiltinType {}     = ErrorCode 8
    errorCode BuiltinTypeNotAStar {}    = ErrorCode 51
    errorCode LexErr {}                 = ErrorCode 6

instance HasErrorCode (UniqueError _a) where
      errorCode FreeVariable {}    = ErrorCode 21
      errorCode IncoherentUsage {} = ErrorCode 12
      errorCode MultiplyDefined {} = ErrorCode 11

instance HasErrorCode (NormCheckError _a _b _c _d _e) where
      errorCode BadTerm {} = ErrorCode 14
      errorCode BadType {} = ErrorCode 13

instance HasErrorCode (TypeError _a _b _c _d) where
    errorCode FreeVariableE {}           = ErrorCode 20
    errorCode FreeTypeVariableE {}       = ErrorCode 19
    errorCode TypeMismatch {}            = ErrorCode 16
    errorCode KindMismatch {}            = ErrorCode 15
    errorCode UnknownBuiltinFunctionE {} = ErrorCode 18

instance HasErrorCode (Error _a _b _c) where
    errorCode (ParseErrorE e)           = errorCode e
    errorCode (UniqueCoherencyErrorE e) = errorCode e
    errorCode (TypeErrorE e)            = errorCode e
    errorCode (NormCheckErrorE e)       = errorCode e
    errorCode (FreeVariableErrorE e)    = errorCode e
