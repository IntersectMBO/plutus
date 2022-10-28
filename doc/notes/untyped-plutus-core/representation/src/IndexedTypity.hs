{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs     #-}
{-# LANGUAGE PolyKinds #-}

module IndexedTypity where

type Constant = ()
type Builtin = ()

data Name   = Name
data TyName = TyName

data Kind = Kind
data Type = Type

data TypedTerm
    = TypedConstant Constant
    | TypedBuiltin Builtin
    | TypedVar Name
    | TypedLamAbs Name Type TypedTerm
    | TypedApply TypedTerm TypedTerm
    | TypedTyAbs TyName Kind TypedTerm
    | TypedTyInst TypedTerm Type
    | TypedUnwrap TypedTerm
    | TypedIWrap Type Type TypedTerm
    | TypedError Type

data UntypedTerm
    = UntypedConstant Constant
    | UntypedBuiltin Builtin
    | UntypedVar Name
    | UntypedLamAbs Name UntypedTerm
    | UntypedApply UntypedTerm UntypedTerm
    | UntypedDelay UntypedTerm
    | UntypedForce UntypedTerm
    | UntypedError

data Typity ty where
    Typed   :: Typity Type
    Untyped :: Typity ()

data Term (typity :: Typity ty) where
    Constant :: Constant -> Term typity
    Builtin :: Builtin -> Term typity
    Var :: Name -> Term typity
    LamAbs :: Name -> ty -> Term typity -> Term (typity :: Typity ty)
    Apply :: Term typity -> Term typity -> Term typity
    TyAbs :: TyName -> Kind -> Term 'Typed -> Term 'Typed
    TyInst :: Term 'Typed -> Type -> Term 'Typed
    Unwrap :: Term 'Typed -> Term 'Typed
    IWrap :: Type -> Type -> Term 'Typed -> Term 'Typed
    Delay :: Term 'Untyped -> Term 'Untyped
    Force :: Term 'Untyped -> Term 'Untyped
    Error :: ty -> Term (typity :: Typity ty)

termToTypedTerm :: Term 'Typed -> TypedTerm
termToTypedTerm = go where
    go (Constant con)         = TypedConstant con
    go (Builtin bn)           = TypedBuiltin bn
    go (Var name)             = TypedVar name
    go (LamAbs name ty body)  = TypedLamAbs name ty (go body)
    go (Apply fun arg)        = TypedApply (go fun) (go arg)
    go (TyAbs name kind body) = TypedTyAbs name kind (go body)
    go (TyInst term ty)       = TypedTyInst (go term) ty
    go (IWrap pat arg term)   = TypedIWrap pat arg (go term)
    go (Unwrap term)          = TypedUnwrap (go term)
    go (Error ty)             = TypedError ty

typedTermToTerm :: TypedTerm -> Term 'Typed
typedTermToTerm = go where
    go (TypedConstant con)         = Constant con
    go (TypedBuiltin bn)           = Builtin bn
    go (TypedVar name)             = Var name
    go (TypedLamAbs name ty body)  = LamAbs name ty (go body)
    go (TypedApply fun arg)        = Apply (go fun) (go arg)
    go (TypedTyAbs name kind body) = TyAbs name kind (go body)
    go (TypedTyInst term ty)       = TyInst (go term) ty
    go (TypedIWrap pat arg term)   = IWrap pat arg (go term)
    go (TypedUnwrap term)          = Unwrap (go term)
    go (TypedError ty)             = Error ty

termToUntypedTerm :: Term 'Untyped -> UntypedTerm
termToUntypedTerm = go where
    go (Constant con)        = UntypedConstant con
    go (Builtin bn)          = UntypedBuiltin bn
    go (Var name)            = UntypedVar name
    go (LamAbs name () body) = UntypedLamAbs name (go body)
    go (Apply fun arg)       = UntypedApply (go fun) (go arg)
    go (Delay term)          = UntypedDelay (go term)
    go (Force term)          = UntypedForce (go term)
    go (Error ())            = UntypedError

untypedTermToTerm :: UntypedTerm -> Term 'Untyped
untypedTermToTerm = go where
    go (UntypedConstant con)     = Constant con
    go (UntypedBuiltin bn)       = Builtin bn
    go (UntypedVar name)         = Var name
    go (UntypedLamAbs name body) = LamAbs name () (go body)
    go (UntypedApply fun arg)    = Apply (go fun) (go arg)
    go (UntypedDelay term)       = Delay (go term)
    go (UntypedForce term)       = Force (go term)
    go UntypedError              = Error ()
