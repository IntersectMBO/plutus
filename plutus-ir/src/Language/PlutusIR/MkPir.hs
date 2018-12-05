
module Language.PlutusIR.MkPir ( Def (..)
                               , TermDef
                               , TypeDef
                               , DatatypeDef
                               , mkVar
                               , mkTyVar
                               , mkIterTyForall
                               , mkIterTyLam
                               , mkIterApp
                               , mkIterTyFun
                               , mkIterLamAbs
                               , mkIterInst
                               , mkIterTyAbs
                               , mkIterTyApp
                               ) where

import           Language.PlutusIR

import           Language.PlutusCore.MkPlc (Def (..), mkTyVar)

import           Data.List                 (foldl')

-- | A term definition as a variable.
type TermDef tyname name a = Def (VarDecl tyname name a) (Term tyname name a)
-- | A type definition as a type variable.
type TypeDef tyname a = Def (TyVarDecl tyname a) (Type tyname a)
-- | A datatype definition as a type variable.
type DatatypeDef tyname name a = Def (TyVarDecl tyname a) (Datatype tyname name a)

-- | Make a 'Var' referencing the given 'VarDecl'.
mkVar :: a -> VarDecl tyname name a -> Term tyname name a
mkVar x = Var x . varDeclName

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
