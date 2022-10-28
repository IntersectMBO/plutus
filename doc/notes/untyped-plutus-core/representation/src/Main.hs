{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies              #-}

module Main where

type Constant = ()
type Builtin = ()

data Name   = Name
data TyName = TyName

data Kind = Kind
data Type = Type

{- Note [Encoding]
'TypedTerm' has the following constructors that 'UntypedTerm' doesn't:

    TypedTyAbs TyName Kind TypedTerm
    TypedTyInst TypedTerm Type
    TypedUnwrap TypedTerm
    TypedIWrap Type Type TypedTerm

'UntypedTerm' has the following constructors that 'TypedTerm' doesn't:

    UntypedDelay UntypedTerm
    UntypedForce UntypedTerm

Both 'TypedTerm' and 'UntypedTerm' have constructors for lambda abstraction and error, but
their contents differs:

    TypedLamAbs Name Type TypedTerm
    TypedError Type

vs

    UntypedLamAbs Name UntypedTerm
    UntypedError

Lambda abstraction and @error@ receive a type in 'TypedTerm', unlike in 'UntypedTerm'.

So there are two kinds of differences:

1. languages have different constructors
2. some constructor are shared, but their contents differ

We can solve both the problems by adopting https://mazzo.li/posts/customizable-data-types.html
I.e. by parameterizing 'Term' over a

    data Typity = Typed | Untyped

such that

    type family ToType (typity :: Typity) where
        ToType 'Typed   = Type
        ToType 'Untyped = ()

so that we can have constructors like

    Term typity
        = <...>
          -- 'TyAbs' only exists if @typity@ is 'Typed'.
        | typity ~ 'Typed => TyAbs TyName Kind (Term typity)
          -- 'Delay' only exists if @typity@ is 'Untyped'.
        | typity ~ 'Untyped => Delay (Term typity)
          -- When @typity@ is 'Typed', @ToType typity@ computes to 'Type'.
          -- When @typity@ is 'Untyped', @ToType typity@ computes to '()', i.e. "no type".
        | LamAbs Name (ToType typity) (Term typity)

Then we can provide

    termToTypedTerm   :: Term 'Typed   -> TypedTerm
    typedTermToTerm   :: TypedTerm     -> Term 'Typed
    termToUntypedTerm :: Term 'Untyped -> UntypedTerm
    untypedTermToTerm :: UntypedTerm   -> Term 'Untyped

and we won't need to match on 'Delay' in 'termToTypedTerm', for example, because 'Delay' only
exists in @Term 'Untyped@ and not @Term 'Typed@. GHC also sees that and doesn't give a
"pattern-match(es) are non-exhaustive" warning (we do have @-Wall@ enabled in this file) for a
'Delay' case missing in 'termToTypedTerm'.
-}

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

data Typity
    = Typed
    | Untyped

type family ToType (typity :: Typity) where
    ToType 'Typed   = Type
    ToType 'Untyped = ()

-- See Note [Encoding].
data Term (typity :: Typity)
    = Constant Constant
    | Builtin Builtin
    | Var Name
    | LamAbs Name (ToType typity) (Term typity)
    | Apply (Term typity) (Term typity)
    | typity ~ 'Typed => TyAbs TyName Kind (Term typity)
    | typity ~ 'Typed => TyInst (Term typity) Type
    | typity ~ 'Typed => Unwrap (Term typity)
    | typity ~ 'Typed => IWrap Type Type (Term typity)
    | typity ~ 'Untyped => Delay (Term typity)
    | typity ~ 'Untyped => Force (Term typity)
    | Error (ToType typity)

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

main :: IO ()
main = mempty
