{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# OPTIONS_GHC -Wno-orphans       #-}
module Language.PlutusIR (
    TyName (..),
    Name (..),
    VarDecl (..),
    TyVarDecl (..),
    varDeclNameString,
    tyVarDeclNameString,
    Kind (..),
    Type (..),
    Datatype (..),
    datatypeNameString,
    Recursivity (..),
    Binding (..),
    Term (..),
    Program (..),
    prettyDef,
    embedIntoIR
    ) where

import           PlutusPrelude

import           Language.PlutusCore        (Kind, Name, TyName, Type)
import qualified Language.PlutusCore        as PLC
import           Language.PlutusCore.MkPlc  (TyVarDecl (..), VarDecl (..))
import qualified Language.PlutusCore.Pretty as PLC

import           GHC.Generics               (Generic)

-- Datatypes

data Datatype tyname name a = Datatype a (TyVarDecl tyname a) [TyVarDecl tyname a] (name a) [VarDecl tyname name a]
    deriving (Functor, Show, Eq, Generic)

varDeclNameString :: VarDecl name Name a -> String
varDeclNameString = bsToStr . PLC.nameString . varDeclName

tyVarDeclNameString :: TyVarDecl TyName a -> String
tyVarDeclNameString = bsToStr . PLC.nameString . PLC.unTyName . tyVarDeclName

datatypeNameString :: Datatype TyName name a -> String
datatypeNameString (Datatype _ tn _ _ _) = tyVarDeclNameString tn

-- Bindings

data Recursivity = NonRec | Rec
    deriving (Show, Eq, Generic)
data Binding tyname name a = TermBind a (VarDecl tyname name a) (Term tyname name a)
                           | TypeBind a (TyVarDecl tyname a) (Type tyname a)
                           | DatatypeBind a (Datatype tyname name a)
    deriving (Functor, Show, Eq, Generic)

-- Terms

{- Note [PIR as a PLC extension]
PIR is designed to be an extension of PLC, which means that we try and be strict superset of it.

The main benefit of this is simplicity, but we hope that in future it will make sharing of
theoretical and practical material easier. In the long run it would be nice if PIR was a "true"
extension of PLC (perhaps in the sense of "Trees that Grow"), and then we could potentially
even share most of the typechecker.
-}

{- Note [Declarations in Plutus Core]
In Plutus Core declarations are usually *flattened*, i.e. `(lam x ty t)`, whereas
in Plutus IR they are *reified*, i.e. `(termBind (vardecl x ty) t)`.

Plutus IR needs reified declarations to make it easier to parse *lists* of declarations,
which occur in a few places.

However, we also include all of Plutus Core's term syntax in our term syntax (and we also use
its types). We therefore have somewhat inconsistent syntax since declarations in Plutus
Core terms will be flattened. This makes the embedding obvious and makes life easier
if we were ever to use the Plutus Core AST "for real".

It would be nice to resolve the inconsistency, but this would probably require changing
Plutus Core to use reified declarations.
-}

-- See note [PIR as a PLC extension]
data Term tyname name a = Let a Recursivity [Binding tyname name a] (Term tyname name a)
                        -- Plutus Core (ish) forms, see note [Declarations in Plutus Core]
                        | Var a (name a)
                        | TyAbs a (tyname a) (Kind a) (Term tyname name a)
                        | LamAbs a (name a) (Type tyname a) (Term tyname name a)
                        | Apply a (Term tyname name a) (Term tyname name a)
                        | Constant a (PLC.Constant a)
                        | TyInst a (Term tyname name a) (Type tyname a)
                        | Error a (Type tyname a)
                        | Wrap a (tyname a) (Type tyname a) (Term tyname name a)
                        | Unwrap a (Term tyname name a)
                        deriving (Functor, Show, Eq, Generic)

embedIntoIR :: PLC.Term tyname name a -> Term tyname name a
embedIntoIR = \case
    PLC.Var a n -> Var a n
    PLC.TyAbs a tn k t -> TyAbs a tn k (embedIntoIR t)
    PLC.LamAbs a n ty t -> LamAbs a n ty (embedIntoIR t)
    PLC.Apply a t1 t2 -> Apply a (embedIntoIR t1) (embedIntoIR t2)
    PLC.Constant a c ->  Constant a c
    PLC.TyInst a t ty -> TyInst a (embedIntoIR t) ty
    PLC.Error a ty -> Error a ty
    PLC.Unwrap a t -> Unwrap a (embedIntoIR t)
    PLC.Wrap a tn ty t -> Wrap a tn ty (embedIntoIR t)

-- no version as PIR is not versioned
data Program tyname name a = Program a (Term tyname name a)

-- Pretty-printing

instance (PLC.PrettyClassicBy configName (tyname a), PLC.PrettyClassicBy configName (name a)) =>
        PrettyBy (PLC.PrettyConfigClassic configName) (VarDecl tyname name a) where
    prettyBy config (VarDecl _ n ty) = parens' ("vardecl" </> vsep' [prettyBy config n, prettyBy config ty])

instance (PLC.PrettyClassicBy configName (tyname a)) =>
        PrettyBy (PLC.PrettyConfigClassic configName) (TyVarDecl tyname a) where
    prettyBy config (TyVarDecl _ n ty) = parens' ("tyvardecl" </> vsep' [prettyBy config n, prettyBy config ty])

instance PrettyBy (PLC.PrettyConfigClassic configName) Recursivity where
    prettyBy _ = \case
        NonRec -> parens' "nonrec"
        Rec -> parens' "rec"

instance (PLC.PrettyClassicBy configName (tyname a), PLC.PrettyClassicBy configName (name a)) =>
        PrettyBy (PLC.PrettyConfigClassic configName) (Datatype tyname name a) where
    prettyBy config (Datatype _ ty tyvars destr constrs) = parens' ("datatype" </> vsep' [
                                                                         prettyBy config ty,
                                                                         vsep' $ fmap (prettyBy config) tyvars,
                                                                         prettyBy config destr,
                                                                         vsep' $ fmap (prettyBy config) constrs])

instance (PLC.PrettyClassicBy configName (tyname a), PLC.PrettyClassicBy configName (name a)) =>
        PrettyBy (PLC.PrettyConfigClassic configName) (Binding tyname name a) where
    prettyBy config = \case
        TermBind _ d t -> parens' ("termbind" </> vsep' [prettyBy config d, prettyBy config t])
        TypeBind _ d ty -> parens' ("typebind" </> vsep' [prettyBy config d, prettyBy config ty])
        DatatypeBind _ d -> parens' ("datatypebind" </> prettyBy config d)

instance (PLC.PrettyClassicBy configName (tyname a), PLC.PrettyClassicBy configName (name a)) =>
        PrettyBy (PLC.PrettyConfigClassic configName) (Term tyname name a) where
    prettyBy config = \case
        Let _ r bs t -> parens' ("let" </> vsep' [prettyBy config r, vsep' $ fmap (prettyBy config) bs, prettyBy config t])
        Var _ n -> prettyBy config n
        TyAbs _ tn k t -> parens' ("abs" </> vsep' [prettyBy config tn, prettyBy config k, prettyBy config t])
        LamAbs _ n ty t -> parens' ("lam" </> vsep' [prettyBy config n, prettyBy config ty, prettyBy config t])
        Apply _ t1 t2 -> brackets' (vsep' [prettyBy config t1, prettyBy config t2])
        Constant _ c -> parens' ("con" </> prettyBy config c)
        TyInst _ t ty -> braces' (vsep' [prettyBy config t, prettyBy config ty])
        Error _ ty -> parens' ("error" </> prettyBy config ty)
        Wrap _ n ty t -> parens' ("wrap" </> vsep' [ prettyBy config n, prettyBy config ty, prettyBy config t ])
        Unwrap _ t -> parens' ("unwrap" </> prettyBy config t)

instance (PLC.PrettyClassicBy configName (tyname a), PLC.PrettyClassicBy configName (name a)) =>
        PrettyBy (PLC.PrettyConfigClassic configName) (Program tyname name a) where
    prettyBy config (Program _ t) = parens' ("program" </> prettyBy config t)

prettyDef :: (PLC.PrettyBy (PLC.PrettyConfigClassic PLC.PrettyConfigName) a) => a -> Doc ann
prettyDef = prettyBy $ PLC.PrettyConfigClassic PLC.defPrettyConfigName
