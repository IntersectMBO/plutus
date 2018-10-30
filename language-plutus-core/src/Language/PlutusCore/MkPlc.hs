
module Language.PlutusCore.MkPlc ( VarDecl (..)
                                 , TyVarDecl (..)
                                 , mkVar
                                 , mkTyVar
                                 , Def (..)
                                 , TermDef
                                 , TypeDef
                                 , mkTermLet
                                 , mkTypeLet
                                 , mkIterTyForall
                                 , mkIterTyLam
                                 , mkIterApp
                                 , mkIterTyFun
                                 , mkIterLamAbs
                                 , mkIterInst
                                 , mkIterTyAbs
                                 , mkIterTyApp
                                 ) where

import           Language.PlutusCore.Type

import           Data.List                (foldl')
import           GHC.Generics             (Generic)

-- | A "variable declaration", i.e. a name and a type for a variable.
data VarDecl tyname name a = VarDecl {varDeclAnn::a, varDeclName::name a, varDeclType::Type tyname a}
    deriving (Functor, Show, Eq, Generic)

-- | Make a 'Var' referencing the given 'VarDecl'.
mkVar :: VarDecl tyname name () -> Term tyname name ()
mkVar = Var () . varDeclName

-- | A "type variable declaration", i.e. a name and a kind for a type variable.
data TyVarDecl tyname a = TyVarDecl {tyVarDeclAnn::a, tyVarDeclName::tyname a, tyVarDeclKind::Kind a}
    deriving (Functor, Show, Eq, Generic)

-- | Make a 'TyVar' referencing the given 'TyVarDecl'.
mkTyVar :: TyVarDecl tyname () -> Type tyname ()
mkTyVar = TyVar () . tyVarDeclName

-- | A definition. Pretty much just a pair with more descriptive names.
data Def var val = Def { defVar::var, defVal::val}

-- | A term definition as a variable.
type TermDef tyname name a = Def (VarDecl tyname name ()) (Term tyname name ())
-- | A type definition as a type variable.
type TypeDef tyname a = Def (TyVarDecl tyname ()) (Type tyname ())

-- | Make a "let-binding" for a term.
mkTermLet
    :: TermDef tyname name ()
    -> Term tyname name () -- ^ The body of the let, possibly referencing the name.
    -> Term tyname name ()
mkTermLet (Def (VarDecl _ name ty) bind) body = Apply () (LamAbs () name ty body) bind

-- | Make a "let-binding" for a type. Note: the body must be a value.
mkTypeLet
    :: TypeDef tyname ()
    -> Term tyname name () -- ^ The body of the let, possibly referencing the name.
    -> Term tyname name ()
mkTypeLet (Def (TyVarDecl _ name k) bind) body = TyInst () (TyAbs () name k body) bind

-- | Make an iterated application.
mkIterApp
    :: Term tyname name () -- ^ @f@
    -> [Term tyname name ()] -- ^@[ x0 ... xn ]@
    -> Term tyname name () -- ^ @[f x0 ... xn ]@
mkIterApp = foldl' (Apply ())

-- | Make an iterated instantiation.
mkIterInst
    :: Term tyname name () -- ^ @a@
    -> [Type tyname ()] -- ^ @ [ x0 ... xn ] @
    -> Term tyname name () -- ^ @{ a x0 ... xn }@
mkIterInst = foldl' (TyInst ())

-- | Lambda abstract a list of names.
mkIterLamAbs
    :: [VarDecl tyname name ()]
    -> Term tyname name ()
    -> Term tyname name ()
mkIterLamAbs args body = foldr (\(VarDecl _ n ty) acc -> LamAbs () n ty acc) body args

-- | Type abstract a list of names.
mkIterTyAbs
    :: [TyVarDecl tyname ()]
    -> Term tyname name ()
    -> Term tyname name ()
mkIterTyAbs args body = foldr (\(TyVarDecl _ n k) acc -> TyAbs () n k acc) body args

-- | Make an iterated type application.
mkIterTyApp
    :: Type tyname () -- ^ @f@
    -> [Type tyname ()] -- ^ @[ x0 ... xn ]@
    -> Type tyname () -- ^ @[ f x0 ... xn ]@
mkIterTyApp = foldl' (TyApp ())

-- | Make an iterated function type.
mkIterTyFun
    :: [Type tyname ()]
    -> Type tyname ()
    -> Type tyname ()
mkIterTyFun tys target = foldr (\ty acc -> TyFun () ty acc) target tys

-- | Universally quantify a list of names.
mkIterTyForall
    :: [TyVarDecl tyname ()]
    -> Type tyname ()
    -> Type tyname ()
mkIterTyForall args body = foldr (\(TyVarDecl _ n k) acc -> TyForall () n k acc) body args

-- | Lambda abstract a list of names.
mkIterTyLam
    :: [TyVarDecl tyname ()]
    -> Type tyname ()
    -> Type tyname ()
mkIterTyLam args body = foldr (\(TyVarDecl _ n k) acc -> TyLam () n k acc) body args
