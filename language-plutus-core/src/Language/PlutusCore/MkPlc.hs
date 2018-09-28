
module Language.PlutusCore.MkPlc where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Type

import           Data.List                (foldl')

-- | Make a "let-binding" for a term.
mkTermLet
    :: name () -- ^ The name for the binding
    -> Term tyname name () -- ^ The term to be bound
    -> Type tyname () -- ^ The type of the term
    -> Term tyname name () -- ^ The body of the let, possibly referencing the name.
    -> Term tyname name ()
mkTermLet name bind ty body = Apply () (LamAbs () name ty body) bind

-- | Make a "let-binding" for a type. Note: the body must be a value.
mkTypeLet
    :: tyname () -- ^ The name for the binding
    -> Type tyname () -- ^ The type to be bound
    -> Kind () -- ^ The kind of the type
    -> Term tyname name () -- ^ The body of the let, possibly referencing the name.
    -> Term tyname name ()
mkTypeLet name bind ty body = TyInst () (TyAbs () name ty body) bind

-- | Make an iterated application.
mkIterApp
    :: Term tyname name ()
    -> [Term tyname name ()]
    -> Term tyname name ()
mkIterApp fun args = foldl' (Apply ()) fun args

-- | Make an iterated instantiation.
mkIterInst
    :: Term tyname name ()
    -> [Type tyname ()]
    -> Term tyname name ()
mkIterInst abs args = foldl' (TyInst ()) abs args

-- | Lambda abstract a list of names.
mkIterLamAbs
    :: [(name (), Type tyname ())]
    -> Term tyname name ()
    -> Term tyname name ()
mkIterLamAbs args body = foldr (\(n, ty) acc -> LamAbs () n ty acc) body args

-- | Type abstract a list of names.
mkIterTyAbs
    :: [(tyname (), Kind ())]
    -> Term tyname name ()
    -> Term tyname name ()
mkIterTyAbs args body = foldr (\(n, ty) acc -> TyAbs () n ty acc) body args

-- | Make an iterated type application.
mkIterTyApp
    :: Type tyname ()
    -> [Type tyname ()]
    -> Type tyname ()
mkIterTyApp fun args = foldl' (TyApp ()) fun args

-- | Make an iterated function type.
mkIterTyFun
    :: [Type tyname ()]
    -> Type tyname ()
    -> Type tyname ()
mkIterTyFun tys target = foldr (\ty acc -> TyFun () ty acc) target tys

-- | Universally quantify a list of names.
mkIterTyForall
    :: [(tyname (), Kind ())]
    -> Type tyname ()
    -> Type tyname ()
mkIterTyForall args body = foldr (\(n, k) acc -> TyForall () n k acc) body args

-- | Lambda abstract a list of names.
mkIterTyLam
    :: [(tyname (), Kind ())]
    -> Type tyname ()
    -> Type tyname ()
mkIterTyLam args body = foldr (\(n, k) acc -> TyLam () n k acc) body args
