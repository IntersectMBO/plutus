# representation

It is possible to unify a typed AST and an untyped one:

```haskell
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
```

See [Main](src/Main.hs) for what this means and how to get there.

An alternative representation is to index `Typity` by what `ToType` maps it to:

```haskell
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
```

See [IndexedTypity](src/IndexedTypity.hs) for full code.

But promoting a GADT is a bit awkward and I'd prefer the former version.

Anyway, I'd like to argue for not unifying the typed AST and the untyped one:

1. the untyped AST and its evaluator are the most important parts of the system, they should be
   simple and readable. Definining a unified evaluator for both the typed AST and the untyped one
   is possible, but results in more complicated code and it's easier to miss something important
   this way (in particular, some corner case) or overcomplicate the code just for the sake of being
   general
2. related to the previous point: compiler writers targeting UPLC don't need to deal with TPLC,
   so unifying the ASTs would add unnecessary noise that those people would need to learn to ignore
3. the current CEK for the typed AST doesn't handle types correctly. By defining the CEK machine
   only over the untyped AST we solve this problem
4. we need to test the untyped evaluator against some typed one, but we have the CK machine for
   that (which doesn't handle types correctly either, but that should be straightforward to fix).
   I think, we don't need to test the untyped evaluator against two equally behaving typed ones
5. we may want to formalize the untyped evaluator by extracting it into Coq/Agda. Then it's best
   to keep it simple (as in "fewer advanced language features used"). Even if we don't want to
   extract Haskell code into a proof assistant, it's still better to keep the code straightforward,
   so that it's easier to match Haskell code with the formalization and check that they agree
