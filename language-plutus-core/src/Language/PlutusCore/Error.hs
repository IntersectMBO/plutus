{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE UndecidableInstances   #-}
-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module Language.PlutusCore.Error
    ( ParseError (..)
    , AsParseError (..)
    , NormalizationError (..)
    , AsNormalizationError (..)
    , UniqueError (..)
    , AsUniqueError (..)
    , RenameError (..)
    , AsRenameError (..)
    , UnknownDynamicBuiltinNameError (..)
    , AsUnknownDynamicBuiltinNameError (..)
    , InternalTypeError (..)
    , AsInternalTypeError (..)
    , TypeError (..)
    , AsTypeError (..)
    , Error (..)
    , AsError (..)
    , throwingEither
    ) where

import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Lens                       hiding (use)
import           Control.Monad.Error.Lens
import           Control.Monad.Except

import qualified Data.Text                          as T
import           Data.Text.Prettyprint.Doc.Internal (Doc (Text))

-- | Lifts an 'Either' into an error context where we can embed the 'Left' value into the error.
throwingEither :: MonadError e m => AReview e t -> Either t a -> m a
throwingEither r e = case e of
    Left t  -> throwing r t
    Right v -> pure v

-- | An error encountered during parsing.
data ParseError a
    = LexErr String
    | Unexpected (Token a)
    | Overflow a Natural Integer
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''ParseError

data UniqueError a
    = MultiplyDefined Unique a a
    | IncoherentUsage Unique a a
    | FreeVariable Unique a
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''UniqueError

data NormalizationError tyname name a
    = BadType a (Type tyname a) T.Text
    | BadTerm a (Term tyname name a) T.Text
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''NormalizationError

-- | A 'RenameError' is thrown when a free variable is encountered during
-- rewriting.
data RenameError a
    = UnboundVar (Name a)
    | UnboundTyVar (TyName a)
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''RenameError

-- | This error is returned whenever scope resolution of a 'DynamicBuiltinName' fails.
newtype UnknownDynamicBuiltinNameError
    = UnknownDynamicBuiltinNameErrorE DynamicBuiltinName
    deriving (Show, Eq, Generic)
    deriving newtype (NFData)
makeClassyPrisms ''UnknownDynamicBuiltinNameError

-- | An internal error occurred during type checking.
data InternalTypeError a
    = OpenTypeOfBuiltin (Type TyName ()) (Builtin ())
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''InternalTypeError

data TypeError a
    = KindMismatch a (Type TyNameWithKind ()) (Kind ()) (Kind ())
    | TypeMismatch a (Term TyNameWithKind NameWithType ())
                     (Type TyNameWithKind ())
                     (NormalizedType TyNameWithKind ())
    | UnknownDynamicBuiltinName a UnknownDynamicBuiltinNameError
    | InternalTypeErrorE a (InternalTypeError a)
    | OutOfGas
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''TypeError

data Error a
    = ParseErrorE (ParseError a)
    | UniqueCoherencyErrorE (UniqueError a)
    | RenameErrorE (RenameError a)
    | TypeErrorE (TypeError a)
    | NormalizationErrorE (NormalizationError TyName Name a)
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''Error

instance AsParseError (Error a) a where
    _ParseError = _ParseErrorE

instance AsUniqueError (Error a) a where
    _UniqueError = _UniqueCoherencyErrorE

instance AsRenameError (Error a) a where
    _RenameError = _RenameErrorE

instance AsTypeError (Error a) a where
    _TypeError = _TypeErrorE

instance AsNormalizationError (Error a) TyName Name a where
    _NormalizationError = _NormalizationErrorE

asInternalError :: Doc ann -> Doc ann
asInternalError doc =
    "An internal error has occurred:" <+> doc <> hardline <>
    "Please report this as a bug."

instance Pretty a => Pretty (ParseError a) where
    pretty (LexErr s)         = "Lexical error:" <+> Text (length s) (T.pack s)
    pretty (Unexpected t)     = "Unexpected" <+> squotes (pretty t) <+> "at" <+> pretty (loc t)
    pretty (Overflow pos _ _) = "Integer overflow at" <+> pretty pos <> "."

instance Pretty a => Pretty (UniqueError a) where
    pretty (MultiplyDefined u def redef) =
        "Variable" <+> pretty u <+> "defined at" <+> pretty def <+> "is redefined at" <+> pretty redef
    pretty (IncoherentUsage u def use) =
        "Variable" <+> pretty u <+> "defined at" <+> pretty def <+> "is used in a different scope at" <+> pretty use
    pretty (FreeVariable u use) =
        "Variable" <+> pretty u <+> "is free at" <+> pretty use

instance (Pretty a, PrettyBy config (Type tyname a), PrettyBy config (Term tyname name a)) =>
        PrettyBy config (NormalizationError tyname name a) where
    prettyBy config (BadType l ty expct) =
        "Malformed type at" <+> pretty l <>
        ". Type" <+>  squotes (prettyBy config ty) <+>
        "is not a" <+> pretty expct <> "."
    prettyBy config (BadTerm l t expct) =
        "Malformed term at" <+> pretty l <>
        ". Term" <+> squotes (prettyBy config t) <+>
        "is not a" <+> pretty expct <> "."

instance (Pretty a, HasPrettyConfigName config) => PrettyBy config (RenameError a) where
    prettyBy config (UnboundVar n@(Name l _ _)) =
        "Error at" <+> pretty l <>
        ". Variable" <+> prettyBy config n <+>
        "is not in scope."
    prettyBy config (UnboundTyVar n@(TyName (Name l _ _))) =
        "Error at" <+> pretty l <>
        ". Type variable" <+> prettyBy config n <+>
        "is not in scope."

instance Pretty UnknownDynamicBuiltinNameError where
    pretty (UnknownDynamicBuiltinNameErrorE dbn) =
        "Scope resolution failed on a dynamic built-in name:" <+> pretty dbn

instance PrettyBy PrettyConfigPlc (InternalTypeError a) where
    prettyBy config (OpenTypeOfBuiltin ty bi)        =
        asInternalError $
            "The type" <+> prettyBy config ty <+>
            "of the" <+> prettyBy config bi <+>
            "built-in is open"

instance Pretty a => PrettyBy PrettyConfigPlc (TypeError a) where
    prettyBy config (KindMismatch x ty k k')          =
        "Kind mismatch at" <+> pretty x <+>
        "in type" <+> squotes (prettyBy config ty) <>
        ". Expected kind" <+> squotes (prettyBy config k) <+>
        ", found kind" <+> squotes (prettyBy config k')
    prettyBy config (TypeMismatch x t ty ty')         =
        "Type mismatch at" <+> pretty x <>
        (if _pcpoCondensedErrors (_pcpOptions config) == CondensedErrorsYes
            then mempty
            else " in term" <> hardline <> indent 2 (squotes (prettyBy config t)) <> ".") <>
        hardline <>
        "Expected type" <> hardline <> indent 2 (squotes (prettyBy config ty)) <>
        "," <> hardline <>
        "found type" <> hardline <> indent 2 (squotes (prettyBy config ty'))
    prettyBy config (InternalTypeErrorE x err)        =
        prettyBy config err <> hardline <>
        "Error location:" <+> pretty x
    prettyBy _      (UnknownDynamicBuiltinName x err) =
        "Unknown dynamic built-in name at" <+> pretty x <>
        ":" <+> pretty err
    prettyBy _      OutOfGas                          = "Type checker ran out of gas."

instance Pretty a => PrettyBy PrettyConfigPlc (Error a) where
    prettyBy _      (ParseErrorE e)           = pretty e
    prettyBy _      (UniqueCoherencyErrorE e) = pretty e
    prettyBy config (RenameErrorE e)          = prettyBy config e
    prettyBy config (TypeErrorE e)            = prettyBy config e
    prettyBy config (NormalizationErrorE e)   = prettyBy config e
