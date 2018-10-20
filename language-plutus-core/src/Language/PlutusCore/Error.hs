{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Error
    ( ParseError (..)
    , NormalizationError (..)
    , RenameError (..)
    , UnknownDynamicBuiltinNameError (..)
    , InternalTypeError (..)
    , TypeError (..)
    , Error (..)
    , IsError (..)
    , convertError
    ) where

import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Type
import           PlutusPrelude

import qualified Data.Text                          as T
import           Data.Text.Prettyprint.Doc.Internal (Doc (Text))

-- | An error encountered during parsing.
data ParseError a
    = LexErr String
    | Unexpected (Token a)
    | Overflow a Natural Integer
    deriving (Show, Eq, Generic, NFData)

data NormalizationError tyname name a
    = BadType a (Type tyname a) T.Text
    | BadTerm a (Term tyname name a) T.Text
    deriving (Show, Eq, Generic, NFData)

-- | A 'RenameError' is thrown when a free variable is encountered during
-- rewriting.
data RenameError a
    = UnboundVar (Name a)
    | UnboundTyVar (TyName a)
    deriving (Show, Eq, Generic, NFData)

-- | This error is returned whenever scope resolution of a 'DynamicBuiltinName' fails.
newtype UnknownDynamicBuiltinNameError
    = UnknownDynamicBuiltinNameError DynamicBuiltinName
    deriving (Show, Eq, Generic)
    deriving newtype (NFData)

-- | An internal error occurred during type checking.
data InternalTypeError a
    = OpenTypeOfBuiltin (Type TyName ()) (Constant ())
    deriving (Show, Eq, Generic, NFData)

data TypeError a
    = KindMismatch { _loc       :: a
                , _inType       :: Type TyNameWithKind ()
                , _expectedKind :: Kind ()
                , _foundKind    :: Kind ()
                }
    | TypeMismatch { _loc       :: a
                , _inTerm       :: Term TyNameWithKind NameWithType ()
                , _expectedType :: Type TyNameWithKind ()
                , _foundType    :: NormalizedType TyNameWithKind ()
                }
    | TyFixMismatch { _loc       :: a
                    , _inTerm    :: Term TyNameWithKind NameWithType ()
                    , _foundType :: NormalizedType TyNameWithKind ()
                    }
    | TyElimMismatch { _loc   :: a
                    , _inTerm :: Term TyNameWithKind NameWithType ()
                    }
    | UnknownDynamicBuiltinName a UnknownDynamicBuiltinNameError
    | InternalTypeError a (InternalTypeError a)
    | OutOfGas
    deriving (Show, Eq, Generic, NFData)

data Error a
    = ParseError (ParseError a)
    | RenameError (RenameError a)
    | TypeError (TypeError a)
    | NormalizationError (NormalizationError TyName Name a)
    deriving (Show, Eq, Generic, NFData)

asInternalError :: Doc ann -> Doc ann
asInternalError doc =
    "An internal error has occurred:" <+> doc <> hardline <>
    "Please report this as a bug."

class IsError f where
    asError :: f a -> Error a

convertError :: IsError f => Either (f a) b -> Either (Error a) b
convertError = first asError

instance IsError Error where
    asError = id

instance IsError ParseError where
    asError = ParseError

instance IsError RenameError where
    asError = RenameError

instance IsError TypeError where
    asError = TypeError

instance IsError (NormalizationError TyName Name) where
    asError = NormalizationError

instance Pretty a => Pretty (ParseError a) where
    pretty (LexErr s)         = "Lexical error:" <+> Text (length s) (T.pack s)
    pretty (Unexpected t)     = "Unexpected" <+> squotes (pretty t) <+> "at" <+> pretty (loc t)
    pretty (Overflow pos _ _) = "Integer overflow at" <+> pretty pos <> "."

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
    pretty (UnknownDynamicBuiltinNameError dbn) =
        "Scope resolution failed on a dynamic built-in name:" <+> pretty dbn

instance PrettyBy PrettyConfigPlc (InternalTypeError a) where
    prettyBy config (OpenTypeOfBuiltin ty con)        =
        asInternalError $
            "The type" <+> prettyBy config ty <+>
            "of the" <+> prettyBy config con <+>
            "built-in is open"

instance Pretty a => PrettyBy PrettyConfigPlc (TypeError a) where
    prettyBy config (KindMismatch x ty k k')            =
        "Kind mismatch at" <+> pretty x <+>
        "in type" <+> squotes (prettyBy config ty) <>
        ". Expected kind" <+> squotes (prettyBy config k) <+>
        ", found kind" <+> squotes (prettyBy config k')
    prettyBy config (TypeMismatch x t ty ty')           =
        "Type mismatch at" <+> pretty x <>
        (if _pcpoCondensedErrors . _pcpOptions $ config
            then mempty
            else " in term" <> hardline <> indent 2 (squotes (prettyBy config t)) <> ".") <>
        hardline <>
        "Expected type" <> hardline <> indent 2 (squotes (prettyBy config ty)) <>
        "," <> hardline <>
        "found type" <> hardline <> indent 2 (squotes (prettyBy config ty'))
    prettyBy config (TyFixMismatch x t ty) =
        "Type mismatch at" <+> pretty x <+>
        (if _pcpoCondensedErrors . _pcpOptions $ config
            then mempty
            else "in term" <> hardline <> indent 2 (squotes (prettyBy config t)) <> ".") <>
        hardline <>
        "Expected type" <> hardline <> indent 2 (squotes "(fix * (fun * *))")
        <> hardline <> "or type"
        <> hardline <> indent 2 (squotes "[(fix * (fun * *)) _]") <> hardline <> "etc." <> hardline <>
        "found type" <+> squotes (prettyBy config ty)
    prettyBy config (TyElimMismatch x t) = "Type elimination mismatch at" <+> pretty x <+>
        (if _pcpoCondensedErrors . _pcpOptions $ config
            then mempty
            else "in term" <> hardline <> indent 2 (squotes (prettyBy config t)) <> ".")
    prettyBy config (InternalTypeError x err)           =
        prettyBy config err <> hardline <>
        "Error location:" <+> pretty x
    prettyBy _      (UnknownDynamicBuiltinName x udbne) =
        "Unknown dynamic built-in at" <+> pretty x <>
        ":" <+> pretty udbne
    prettyBy _      OutOfGas                            = "Type checker ran out of gas."

instance Pretty a => PrettyBy PrettyConfigPlc (Error a) where
    prettyBy _      (ParseError e)         = pretty e
    prettyBy config (RenameError e)        = prettyBy config e
    prettyBy config (TypeError e)          = prettyBy config e
    prettyBy config (NormalizationError e) = prettyBy config e
