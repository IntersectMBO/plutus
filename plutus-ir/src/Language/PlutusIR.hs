{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
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
    typeSubtypes,
    Datatype (..),
    datatypeNameString,
    Recursivity (..),
    Strictness (..),
    Binding (..),
    bindingSubterms,
    bindingSubtypes,
    Term (..),
    termSubterms,
    termSubtypes,
    termBindings,
    Program (..)
    ) where

import           PlutusPrelude

import           Language.PlutusCore        (Kind, Name, TyName, Type (..), typeSubtypes)
import qualified Language.PlutusCore        as PLC
import           Language.PlutusCore.CBOR   ()
import           Language.PlutusCore.MkPlc  (Def (..), TermLike (..), TyVarDecl (..), VarDecl (..))
import qualified Language.PlutusCore.Pretty as PLC

import           Control.Lens               hiding (Strict)

import           Codec.Serialise            (Serialise)

import qualified Data.Text                  as T

-- Datatypes

{- Note: [Serialization of PIR]
The serialized version of Plutus-IR will be included in  the final
executable for helping debugging and testing and providing better error
reporting. It is not meant to be stored on the chain, which means that
the underlying representation can vary. The `Generic` instances of the
terms can thus be used as backwards compatibility is not required.
-}

data Datatype tyname name uni a = Datatype a (TyVarDecl tyname a) [TyVarDecl tyname a] (name a) [VarDecl tyname name uni a]
    deriving (Functor, Show, Generic)

instance ( PLC.Closed uni
         , uni `PLC.Everywhere` Serialise
         , Serialise a
         , Serialise (tyname a)
         , Serialise (name a)
         ) => Serialise (Datatype tyname name uni a)

varDeclNameString :: VarDecl tyname Name uni a -> String
varDeclNameString = T.unpack . PLC.nameString . varDeclName

tyVarDeclNameString :: TyVarDecl TyName a -> String
tyVarDeclNameString = T.unpack . PLC.nameString . PLC.unTyName . tyVarDeclName

datatypeNameString :: Datatype TyName name uni a -> String
datatypeNameString (Datatype _ tn _ _ _) = tyVarDeclNameString tn

-- Bindings

data Recursivity = NonRec | Rec
    deriving (Show, Eq, Generic)

instance Serialise Recursivity

data Strictness = NonStrict | Strict
    deriving (Show, Eq, Generic)

instance Serialise Strictness

data Binding tyname name uni a = TermBind a Strictness (VarDecl tyname name uni a) (Term tyname name uni a)
                           | TypeBind a (TyVarDecl tyname a) (Type tyname uni a)
                           | DatatypeBind a (Datatype tyname name uni a)
    deriving (Functor, Show, Generic)

instance ( PLC.Closed uni
         , uni `PLC.Everywhere` Serialise
         , Serialise a
         , Serialise (tyname a)
         , Serialise (name a)
         ) => Serialise (Binding tyname name uni a)

{-# INLINE bindingSubterms #-}
-- | Get all the direct child 'Term's of the given 'Binding'.
bindingSubterms :: Traversal' (Binding tyname name uni a) (Term tyname name uni a)
bindingSubterms f = \case
    TermBind x s d t -> TermBind x s d <$> f t
    b@TypeBind {} -> pure b
    d@DatatypeBind {} -> pure d

{-# INLINE varDeclSubtypes #-}
-- | Get all the direct child 'Type's of the given 'VarDecl'.
varDeclSubtypes :: Traversal' (VarDecl tyname name uni a) (Type tyname uni a)
varDeclSubtypes f (VarDecl a n ty) = VarDecl a n <$> f ty

{-# INLINE datatypeSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Datatype'.
datatypeSubtypes :: Traversal' (Datatype tyname name uni a) (Type tyname uni a)
datatypeSubtypes f (Datatype a n vs m cs) = Datatype a n vs m <$> (traverse . varDeclSubtypes) f cs

{-# INLINE bindingSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Binding'.
bindingSubtypes :: Traversal' (Binding tyname name uni a) (Type tyname uni a)
bindingSubtypes f = \case
    TermBind x s d t -> TermBind x s <$> varDeclSubtypes f d <*> pure t
    DatatypeBind x d -> DatatypeBind x <$> datatypeSubtypes f d
    TypeBind a d ty -> TypeBind a d <$> f ty

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
data Term tyname name uni a =
                        -- Plutus Core (ish) forms, see note [Declarations in Plutus Core]
                          Let a Recursivity (NonEmpty (Binding tyname name uni a)) (Term tyname name uni a)
                        | Var a (name a)
                        | TyAbs a (tyname a) (Kind a) (Term tyname name uni a)
                        | LamAbs a (name a) (Type tyname uni a) (Term tyname name uni a)
                        | Apply a (Term tyname name uni a) (Term tyname name uni a)
                        | Constant a (PLC.Some (PLC.ValueOf uni))
                        | Builtin a (PLC.Builtin a)
                        | TyInst a (Term tyname name uni a) (Type tyname uni a)
                        | Error a (Type tyname uni a)
                        | IWrap a (Type tyname uni a) (Type tyname uni a) (Term tyname name uni a)
                        | Unwrap a (Term tyname name uni a)
                        deriving (Functor, Show, Generic)

instance ( PLC.Closed uni
         , uni `PLC.Everywhere` Serialise
         , Serialise a
         , Serialise (tyname a)
         , Serialise (name a)
         ) => Serialise (Term tyname name uni a)

instance TermLike (Term tyname name uni) tyname name uni where
    var      = Var
    tyAbs    = TyAbs
    lamAbs   = LamAbs
    apply    = Apply
    constant = Constant
    builtin  = Builtin
    tyInst   = TyInst
    unwrap   = Unwrap
    iWrap    = IWrap
    error    = Error
    termLet x (Def vd bind) = Let x NonRec (pure $ TermBind x Strict vd bind)
    typeLet x (Def vd bind) = Let x NonRec (pure $ TypeBind x vd bind)

{-# INLINE termSubterms #-}
-- | Get all the direct child 'Term's of the given 'Term', including those within 'Binding's.
termSubterms :: Traversal' (Term tyname name uni a) (Term tyname name uni a)
termSubterms f = \case
    Let x r bs t -> Let x r <$> (traverse . bindingSubterms) f bs <*> f t
    TyAbs x tn k t -> TyAbs x tn k <$> f t
    LamAbs x n ty t -> LamAbs x n ty <$> f t
    Apply x t1 t2 -> Apply x <$> f t1 <*> f t2
    TyInst x t ty -> TyInst x <$> f t <*> pure ty
    IWrap x ty1 ty2 t -> IWrap x ty1 ty2 <$> f t
    Unwrap x t -> Unwrap x <$> f t
    e@Error {} -> pure e
    v@Var {} -> pure v
    c@Constant {} -> pure c
    b@Builtin {} -> pure b

{-# INLINE termSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Term', including those within 'Binding's.
termSubtypes :: Traversal' (Term tyname name uni a) (Type tyname uni a)
termSubtypes f = \case
    Let x r bs t -> Let x r <$> (traverse . bindingSubtypes) f bs <*> pure t
    LamAbs x n ty t -> LamAbs x n <$> f ty <*> pure t
    TyInst x t ty -> TyInst x t <$> f ty
    IWrap x ty1 ty2 t -> IWrap x <$> f ty1 <*> f ty2 <*> pure t
    Error x ty -> Error x <$> f ty
    t@TyAbs {} -> pure t
    a@Apply {} -> pure a
    u@Unwrap {} -> pure u
    v@Var {} -> pure v
    c@Constant {} -> pure c
    b@Builtin {} -> pure b

{-# INLINE termBindings #-}
-- | Get all the direct child 'Binding's of the given 'Term'.
termBindings :: Traversal' (Term tyname name uni a) (Binding tyname name uni a)
termBindings f = \case
    Let x r bs t -> Let x r <$> traverse f bs <*> pure t
    t -> pure t

-- no version as PIR is not versioned
data Program tyname name uni a = Program a (Term tyname name uni a) deriving Generic

instance ( PLC.Closed uni
         , uni `PLC.Everywhere` Serialise
         , Serialise a
         , Serialise (tyname a)
         , Serialise (name a)
         ) => Serialise (Program tyname name uni a)

-- Pretty-printing

instance ( PLC.PrettyClassicBy configName (tyname a)
         , PLC.PrettyClassicBy configName (name a)
         , PLC.GShow uni, uni `PLC.Everywhere` PLC.PrettyConst
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (VarDecl tyname name uni a) where
    prettyBy config (VarDecl _ n ty) = parens' ("vardecl" </> vsep' [prettyBy config n, prettyBy config ty])

instance (PLC.PrettyClassicBy configName (tyname a)) =>
        PrettyBy (PLC.PrettyConfigClassic configName) (TyVarDecl tyname a) where
    prettyBy config (TyVarDecl _ n ty) = parens' ("tyvardecl" </> vsep' [prettyBy config n, prettyBy config ty])

instance PrettyBy (PLC.PrettyConfigClassic configName) Recursivity where
    prettyBy _ = \case
        NonRec -> parens' "nonrec"
        Rec -> parens' "rec"

instance PrettyBy (PLC.PrettyConfigClassic configName) Strictness where
    prettyBy _ = \case
        NonStrict -> parens' "nonstrict"
        Strict -> parens' "strict"

instance ( PLC.PrettyClassicBy configName (tyname a)
         , PLC.PrettyClassicBy configName (name a)
         , PLC.GShow uni, uni `PLC.Everywhere` PLC.PrettyConst
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (Datatype tyname name uni a) where
    prettyBy config (Datatype _ ty tyvars destr constrs) = parens' ("datatype" </> vsep' [
                                                                         prettyBy config ty,
                                                                         vsep' $ fmap (prettyBy config) tyvars,
                                                                         prettyBy config destr,
                                                                         vsep' $ fmap (prettyBy config) constrs])

instance ( PLC.PrettyClassicBy configName (tyname a)
         , PLC.PrettyClassicBy configName (name a)
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (Binding tyname name uni a) where
    prettyBy config = \case
        TermBind _ s d t -> parens' ("termbind" </> vsep' [prettyBy config s, prettyBy config d, prettyBy config t])
        TypeBind _ d ty -> parens' ("typebind" </> vsep' [prettyBy config d, prettyBy config ty])
        DatatypeBind _ d -> parens' ("datatypebind" </> prettyBy config d)

instance ( PLC.PrettyClassicBy configName (tyname a)
         , PLC.PrettyClassicBy configName (name a)
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (Term tyname name uni a) where
    prettyBy config = \case
        Let _ r bs t -> parens' ("let" </> vsep' [prettyBy config r, vsep' . toList $ fmap (prettyBy config) bs, prettyBy config t])
        Var _ n -> prettyBy config n
        TyAbs _ tn k t -> parens' ("abs" </> vsep' [prettyBy config tn, prettyBy config k, prettyBy config t])
        LamAbs _ n ty t -> parens' ("lam" </> vsep' [prettyBy config n, prettyBy config ty, prettyBy config t])
        Apply _ t1 t2 -> brackets' (vsep' [prettyBy config t1, prettyBy config t2])
        Constant _ c -> parens' ("con" </> pretty c)
        Builtin _ bi -> parens' ("builtin" </> pretty bi)
        TyInst _ t ty -> braces' (vsep' [prettyBy config t, prettyBy config ty])
        Error _ ty -> parens' ("error" </> prettyBy config ty)
        IWrap _ ty1 ty2 t -> parens' ("iwrap" </> vsep' [ prettyBy config ty1, prettyBy config ty2, prettyBy config t ])
        Unwrap _ t -> parens' ("unwrap" </> prettyBy config t)

instance ( PLC.PrettyClassicBy configName (tyname a)
         , PLC.PrettyClassicBy configName (name a)
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         ) => PrettyBy (PLC.PrettyConfigClassic configName) (Program tyname name uni a) where
    prettyBy config (Program _ t) = parens' ("program" </> prettyBy config t)

-- See note [Default pretty instances for PLC]
instance (PLC.PrettyClassic (tyname a)) =>
    Pretty (TyVarDecl tyname a) where
    pretty = PLC.prettyClassicDef

instance ( PLC.PrettyClassic (tyname a)
         , PLC.PrettyClassic (name a)
         , PLC.GShow uni, uni `PLC.Everywhere` PLC.PrettyConst
         ) => Pretty (VarDecl tyname name uni a) where
    pretty = PLC.prettyClassicDef

instance ( PLC.PrettyClassic (tyname a)
         , PLC.PrettyClassic (name a)
         , PLC.GShow uni, uni `PLC.Everywhere` PLC.PrettyConst
         ) => Pretty (Datatype tyname name uni a) where
    pretty = PLC.prettyClassicDef

instance ( PLC.PrettyClassic (tyname a)
         , PLC.PrettyClassic (name a)
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         ) => Pretty (Binding tyname name uni a) where
    pretty = PLC.prettyClassicDef

instance ( PLC.PrettyClassic (tyname a)
         , PLC.PrettyClassic (name a)
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         ) => Pretty (Term tyname name uni a) where
    pretty = PLC.prettyClassicDef

instance ( PLC.PrettyClassic (tyname a)
         , PLC.PrettyClassic (name a)
         , PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
         ) => Pretty (Program tyname name uni a) where
    pretty = PLC.prettyClassicDef
