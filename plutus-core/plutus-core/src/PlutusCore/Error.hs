{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- appears in the generated instances

module PlutusCore.Error
  ( ParserError (..)
  , ParserErrorBundle (..)
  , NormCheckError (..)
  , UniqueError (..)
  , ExpectedShapeOr (..)
  , TypeError (..)
  , FreeVariableError (..)
  , Error (..)
  , throwingEither
  , ShowErrorComponent (..)
  , ApplyProgramError (..)
  ) where

import PlutusPrelude

import PlutusCore.Core
import PlutusCore.DeBruijn.Internal
import PlutusCore.Name.Unique
import PlutusCore.Pretty
import Prettyprinter.Custom (sexp)

import Control.Lens hiding (use)
import Control.Monad.Error.Lens
import Control.Monad.Except
import Data.Text qualified as T
import PlutusCore.Annotation (SrcSpan)
import Prettyprinter (hardline, hsep, indent, squotes, (<+>))
import Text.Megaparsec as M
import Universe

-- | Lifts an 'Either' into an error context where we can embed the 'Left' value into the error.
throwingEither :: MonadError e m => AReview e t -> Either t a -> m a
throwingEither r e = case e of
  Left t -> throwing r t
  Right v -> pure v

-- | An error encountered during parsing.
data ParserError
  = BuiltinTypeNotAStar !T.Text !SourcePos
  | UnknownBuiltinFunction !T.Text !SourcePos ![T.Text]
  | InvalidBuiltinConstant !T.Text !T.Text !SourcePos
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (NFData)

instance Show ParserError where
  show = show . pretty

data UniqueError ann
  = MultiplyDefined !Unique !ann !ann
  | IncoherentUsage !Unique !ann !ann
  | FreeVariable !Unique !ann
  deriving stock (Show, Eq, Generic, Functor)
  deriving anyclass (NFData)

instance Exception (UniqueError SrcSpan)

data NormCheckError tyname name uni fun ann
  = BadType !ann !(Type tyname uni ann) !T.Text
  | BadTerm !ann !(Term tyname name uni fun ann) !T.Text
  deriving stock (Functor, Generic)

deriving anyclass instance
  (NFData tyname, NFData name, Closed uni, Everywhere uni NFData, NFData fun, NFData ann)
  => NFData (NormCheckError tyname name uni fun ann)

deriving stock instance
  (Show tyname, Show name, Closed uni, Everywhere uni Show, Show fun, Show ann, GShow uni)
  => Show (NormCheckError tyname name uni fun ann)

deriving stock instance
  ( Eq (Term tyname name uni fun ann)
  , Eq (Type tyname uni ann)
  , GEq uni
  , Closed uni
  , uni `Everywhere` Eq
  , Eq fun
  , Eq ann
  )
  => Eq (NormCheckError tyname name uni fun ann)

{-| This is needed for nice kind/type checking error messages. In some cases the type checker knows
the exact type that an expression has to have for type checking to succeed (see any of
'checkTypeM' functions and its usages), which is what 'ExpectedExact' is suitable for. In other
cases the type checker only cares about the shape of the inferred type, e.g. the type checker
knows that the type of a function has to be @dom -> cod@ for type checking to succeed, but it
doesn't yet care what @dom@ and @cod@ exactly are. Which is what 'ExpectedShape' is useful for as
it allows one to specify the shape of an expected type with some existential variables in it when
it's impossible to provide an exact type. -}
data ExpectedShapeOr a
  = ExpectedShape
      !T.Text
      -- ^ The expected shape potentially referencing existential variables.
      ![T.Text]
      -- ^ The list of existential variables.
  | ExpectedExact !a
  deriving stock (Show, Eq, Generic, Functor)
  deriving anyclass (NFData)

data TypeError term uni fun ann
  = KindMismatch
      !ann
      !(Type TyName uni ())
      !(ExpectedShapeOr (Kind ()))
      -- ^ The expected type or the shape of a kind.
      !(Kind ())
      -- ^ The actual kind.
  | TypeMismatch
      !ann
      !term
      !(ExpectedShapeOr (Type TyName uni ()))
      -- ^ The expected type or the shape of a type.
      !(Normalized (Type TyName uni ()))
      -- ^ The actual type.
  | TyNameMismatch !ann !TyName !TyName
  | NameMismatch !ann !Name !Name
  | FreeTypeVariableE !ann !TyName
  | FreeVariableE !ann !Name
  | UnknownBuiltinFunctionE !ann !fun
  | UnsupportedCaseBuiltin !ann !T.Text
  deriving stock (Show, Eq, Generic, Functor)
  deriving anyclass (NFData)

-- Make a custom data type and wrap @ParseErrorBundle@ in it so I can use @makeClassyPrisms@
-- on @ParseErrorBundle@.
-- TODO: this can be killed
newtype ParserErrorBundle
  = ParseErrorB !(ParseErrorBundle T.Text ParserError)
  deriving stock (Eq, Generic)
  deriving anyclass (NFData)

instance Pretty ParserErrorBundle where
  pretty (ParseErrorB err) = pretty $ errorBundlePretty err

instance Show ParserErrorBundle where
  show (ParseErrorB peb) = errorBundlePretty peb

data Error uni fun ann
  = ParseErrorE !ParserErrorBundle
  | UniqueCoherencyErrorE !(UniqueError ann)
  | TypeErrorE !(TypeError (Term TyName Name uni fun ()) uni fun ann)
  | NormCheckErrorE !(NormCheckError TyName Name uni fun ann)
  | FreeVariableErrorE !FreeVariableError
  deriving stock (Generic, Functor)

deriving stock instance
  (Eq fun, Eq ann, Closed uni, Everywhere uni Eq, GEq uni, Eq ParserError)
  => Eq (Error uni fun ann)

deriving anyclass instance
  (NFData fun, NFData ann, Closed uni, Everywhere uni NFData, NFData ParserError)
  => NFData (Error uni fun ann)

deriving stock instance
  (Show fun, Show ann, Closed uni, Everywhere uni Show, GShow uni, Show ParserError)
  => Show (Error uni fun ann)

instance Pretty SourcePos where
  pretty = pretty . sourcePosPretty

instance Pretty ParserError where
  pretty (BuiltinTypeNotAStar ty loc) =
    "Expected a type of kind star (to later parse a constant), but got:"
      <+> squotes (pretty ty)
      <+> "at"
      <+> pretty loc
  pretty (UnknownBuiltinFunction s loc lBuiltin) =
    "Unknown built-in function"
      <+> squotes (pretty s)
      <+> "at"
      <+> pretty loc
      <> "."
      <> hardline
      <> "Parsable functions are "
      <+> pretty lBuiltin
  pretty (InvalidBuiltinConstant c s loc) =
    "Invalid constant"
      <+> squotes (pretty c)
      <+> "of type"
      <+> squotes (pretty s)
      <+> "at"
      <+> pretty loc

instance ShowErrorComponent ParserError where
  showErrorComponent = show . pretty

instance Pretty ann => Pretty (UniqueError ann) where
  pretty (MultiplyDefined u defd redefd) =
    "Variable"
      <+> pretty u
      <+> "defined at"
      <+> pretty defd
      <+> "is redefined at"
      <+> pretty redefd
  pretty (IncoherentUsage u defd use) =
    "Variable"
      <+> pretty u
      <+> "defined at"
      <+> pretty defd
      <+> "is used in a different scope at"
      <+> pretty use
  pretty (FreeVariable u use) =
    "Variable" <+> pretty u <+> "is free at" <+> pretty use

instance
  ( Pretty ann
  , PrettyBy config (Type tyname uni ann)
  , PrettyBy config (Term tyname name uni fun ann)
  )
  => PrettyBy config (NormCheckError tyname name uni fun ann)
  where
  prettyBy config (BadType ann ty expct) =
    "Malformed type at"
      <+> pretty ann
      <> ". Type"
      <+> squotes (prettyBy config ty)
      <+> "is not a"
      <+> pretty expct
      <> "."
  prettyBy config (BadTerm ann t expct) =
    "Malformed term at"
      <+> pretty ann
      <> ". Term"
      <+> squotes (prettyBy config t)
      <+> "is not a"
      <+> pretty expct
      <> "."

{-| Align a list of existential variables in a pretty way.

>>> :set -XOverloadedStrings
>>> existentialVars []
>>> existentialVars ["'a'"]
 for some 'a'
>>> existentialVars ["'a'", "'b'"]
 for some 'a' and 'b'
>>> existentialVars ["'a'", "'b'", "'c'"]
 for some 'a', 'b' and 'c' -}
existentialVars :: [Doc ann] -> Doc ann
existentialVars [] = ""
existentialVars (x0 : xs0) = " for some " <> go x0 xs0
  where
    go x [] = x
    go x [y] = x <> " and " <> y
    go x (y : xs) = x <> ", " <> go y xs

instance PrettyBy PrettyConfigPlc a => PrettyBy PrettyConfigPlc (ExpectedShapeOr a) where
  prettyBy _ (ExpectedShape shape vars) =
    squotes (sexp (pretty shape) []) <> existentialVars (map (squotes . pretty) vars)
  prettyBy config (ExpectedExact thing) = squotes (prettyBy config thing)

instance
  (Pretty term, PrettyUni uni, Pretty fun, Pretty ann)
  => PrettyBy PrettyConfigPlc (TypeError term uni fun ann)
  where
  prettyBy config (KindMismatch ann ty shapeOrK k') =
    "Kind mismatch at"
      <+> pretty ann
      <> hardline
      <> "Expected a type of kind"
      <> hardline
      <> indent 2 (prettyBy config shapeOrK)
      <> hardline
      <> "But found one of kind"
      <> hardline
      <> indent 2 (squotes (prettyBy config k'))
      <> hardline
      <> "Namely,"
      <> hardline
      <> indent 2 (squotes (prettyBy config ty))
  prettyBy config (TypeMismatch ann t shapeOrTy ty') =
    "Type mismatch at"
      <+> pretty ann
      <> hardline
      <> "Expected a term of type"
      <> hardline
      <> indent 2 (prettyBy config shapeOrTy)
      <> hardline
      <> "But found one of type"
      <> hardline
      <> indent 2 (squotes (prettyBy config ty'))
      <> ( if _pcpoCondensedErrors (_pcpOptions config) == CondensedErrorsYes
             then mempty
             -- TODO: we should use prettyBy here but the problem is
             -- that `instance PrettyClassic PIR.Term` whereas `instance PrettyPLC PLC.Term`
             else hardline <> "Namely," <> hardline <> indent 2 (squotes (pretty t))
         )
  prettyBy config (FreeTypeVariableE ann name) =
    "Free type variable at " <+> pretty ann <+> ": " <+> prettyBy config name
  prettyBy config (FreeVariableE ann name) =
    "Free variable at " <+> pretty ann <+> ": " <+> prettyBy config name
  prettyBy _ (UnknownBuiltinFunctionE ann fun) =
    "An unknown built-in function at" <+> pretty ann <> ":" <+> pretty fun
  prettyBy _ (TyNameMismatch ann name1 name2) =
    hsep
      [ "Type-level name mismatch at"
      , pretty ann <> ":"
      , pretty $ name1 ^. theText
      , "is in scope, but"
      , pretty $ name2 ^. theText
      , "having the same Unique"
      , pretty $ name1 ^. theUnique
      , "is attempted to be referenced"
      ]
  prettyBy _ (NameMismatch ann name1 name2) =
    hsep
      [ "Term-level name mismatch at"
      , pretty ann <> ":"
      , pretty $ name1 ^. theText
      , "is in scope, but"
      , pretty $ name2 ^. theText
      , "having the same Unique"
      , pretty $ name1 ^. theUnique
      , "is attempted to be referenced"
      ]
  prettyBy _ (UnsupportedCaseBuiltin ann err) =
    hsep
      [ "Unsupported 'case' of a value of a built-in type at"
      , pretty ann <> ":"
      , hardline
      , pretty err
      ]

instance
  (PrettyUni uni, Pretty fun, Pretty ann)
  => PrettyBy PrettyConfigPlc (Error uni fun ann)
  where
  prettyBy _ (ParseErrorE e) = pretty e
  prettyBy _ (UniqueCoherencyErrorE e) = pretty e
  prettyBy config (TypeErrorE e) = prettyBy config e
  prettyBy config (NormCheckErrorE e) = prettyBy config e
  prettyBy _ (FreeVariableErrorE e) = pretty e

-- | Errors from `applyProgram` for PIR, PLC, UPLC.
data ApplyProgramError
  = MkApplyProgramError Version Version

instance Show ApplyProgramError where
  show (MkApplyProgramError v1 v2) =
    "Cannot apply two programs together: the first program has version "
      <> show v1
      <> " but the second program has version "
      <> show v2

instance Exception ApplyProgramError
