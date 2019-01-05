
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
mkVar :: a -> VarDecl tyname name a -> Term tyname name a
mkVar x = Var x . varDeclName

-- | A "type variable declaration", i.e. a name and a kind for a type variable.
data TyVarDecl tyname a = TyVarDecl {tyVarDeclAnn::a, tyVarDeclName::tyname a, tyVarDeclKind::Kind a}
    deriving (Functor, Show, Eq, Generic)

-- | Make a 'TyVar' referencing the given 'TyVarDecl'.
mkTyVar :: a -> TyVarDecl tyname a -> Type tyname a
mkTyVar x = TyVar x . tyVarDeclName

-- | A definition. Pretty much just a pair with more descriptive names.
data Def var val = Def { defVar::var, defVal::val} deriving (Show, Eq, Ord, Generic)

-- | A term definition as a variable.
type TermDef tyname name a = Def (VarDecl tyname name a) (Term tyname name a)
-- | A type definition as a type variable.
type TypeDef tyname a = Def (TyVarDecl tyname a) (Type tyname a)

-- | Make a "let-binding" for a term.
mkTermLet
    :: a
    -> TermDef tyname name a
    -> Term tyname name a -- ^ The body of the let, possibly referencing the name.
    -> Term tyname name a
mkTermLet x (Def (VarDecl _ name ty) bind) body = Apply x (LamAbs x name ty body) bind

-- | Make a "let-binding" for a type. Note: the body must be a value.
mkTypeLet
    :: a
    -> TypeDef tyname a
    -> Term tyname name a -- ^ The body of the let, possibly referencing the name.
    -> Term tyname name a
mkTypeLet x (Def (TyVarDecl _ name k) bind) body = TyInst x (TyAbs x name k body) bind

-- | Make an iterated application.
mkIterApp
    :: a
    -> Term tyname name a -- ^ @f@
    -> [Term tyname name a] -- ^@[ x0 ... xn ]@
    -> Term tyname name a -- ^ @[f x0 ... xn ]@
mkIterApp x = foldl' (Apply x)

-- | Make an iterated instantiation.
mkIterInst
    :: a
    -> Term tyname name a -- ^ @a@
    -> [Type tyname a] -- ^ @ [ x0 ... xn ] @
    -> Term tyname name a -- ^ @{ a x0 ... xn }@
mkIterInst x = foldl' (TyInst x)

-- | Lambda abstract a list of names.
mkIterLamAbs
    :: a
    -> [VarDecl tyname name a]
    -> Term tyname name a
    -> Term tyname name a
mkIterLamAbs x args body = foldr (\(VarDecl _ n ty) acc -> LamAbs x n ty acc) body args

-- | Type abstract a list of names.
mkIterTyAbs
    :: a
    -> [TyVarDecl tyname a]
    -> Term tyname name a
    -> Term tyname name a
mkIterTyAbs x args body = foldr (\(TyVarDecl _ n k) acc -> TyAbs x n k acc) body args

-- | Make an iterated type application.
mkIterTyApp
    :: a
    -> Type tyname a -- ^ @f@
    -> [Type tyname a] -- ^ @[ x0 ... xn ]@
    -> Type tyname a -- ^ @[ f x0 ... xn ]@
mkIterTyApp x = foldl' (TyApp x)

-- | Make an iterated function type.
mkIterTyFun
    :: a
    -> [Type tyname a]
    -> Type tyname a
    -> Type tyname a
mkIterTyFun x tys target = foldr (\ty acc -> TyFun x ty acc) target tys

-- | Universally quantify a list of names.
mkIterTyForall
    :: a
    -> [TyVarDecl tyname a]
    -> Type tyname a
    -> Type tyname a
mkIterTyForall x args body = foldr (\(TyVarDecl _ n k) acc -> TyForall x n k acc) body args

-- | Lambda abstract a list of names.
mkIterTyLam
    :: a
    -> [TyVarDecl tyname a]
    -> Type tyname a
    -> Type tyname a
mkIterTyLam x args body = foldr (\(TyVarDecl _ n k) acc -> TyLam x n k acc) body args
