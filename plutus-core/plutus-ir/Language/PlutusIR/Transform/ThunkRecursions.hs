{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
-- | Implements a PIR-to-PIR transformation that makes all recursive term definitions
-- compilable to PLC. See Note [Thunking recursions] for details.
module Language.PlutusIR.Transform.ThunkRecursions (thunkRecursions) where

import           PlutusPrelude

import           Language.PlutusIR

{- Note [Thunking recursions]
Our fixpoint combinators in Plutus Core know how to handle mutually recursive values
of *function type*. That is, we can define `map : List Int -> List Int` but *not*
`map : forall a . List a -> List a`, because the latter has a universally
qualified type, instead of a function type (although it is a function underneath).

We could solve this problem for universally quantified values by lifting the forall
out of the recursion. This is a bit like performing the following transformation:

    map : forall a b . (a -> b) -> List a -> List b
    map f xs = case xs of
        [] -> []
        x:xs -> f x : map f xs

vs

    -- non-recursive
    map : forall a b . (a -> b) -> List a -> List a
    map = map'
        where
            -- recursive, but *monomorphic* in the 'a' and 'b' we instantiate to, so of
            -- simple function type
            map' : (a -> b) -> List a -> List b
            map' f xs = case xs of
                [] -> []
                x:xs -> f x : map' f xs

However, this has two drawbacks:
- It only works for polymorphic functions. There are other kinds of non-function
  values which we might want to define recursively.
- It doesn't work if we use polymorphic recursion, because the function we are
  defining is monomorphic, so the recursive call must be at the same type.

The latter is quite annoying, because in practice all interesting functions over
irregular datatypes will use polymorphic recursion, and we've gone to some lengths
to allow ourselves to define irregular datatypes.

The alternative solution is: given a proposed recursive definition of a value of
non-function type, we simply *make* it into a value of function type, by adding
a unit argument and forcing it at all the uses in the body.

So we do something like this:

    -- non-recursive, acts as an "adaptor" for other consumers of the original function
    map : forall a b . (a -> b) -> List a -> List b
    map = map' () @a
        where
            -- recursive, but thunked, so of simple function type
            map' : () -> forall a' b' . (a' -> b') -> List a' -> List b'
            map' _ f xs = case xs of
                [] -> []
                x:xs -> f x : (map' () @b) f xs

This has the advantage of always working, but it's annoying because we have to go
in and edit the body of the function definition.

Fortunately, we can implement this quite simply by using another feature of PIR: non-strict
let bindings. Non-strict let bindings are exactly delayed like this, so we can simply toggle
any recursive, non-function bindings to become non-strict bindings.
-}

isFunctionType :: Type tyname uni a -> Bool
isFunctionType = \case
    TyFun {} -> True
    _ -> False

thunkBinding :: Binding tyname name uni fun a -> Binding tyname name uni fun a
thunkBinding = \case
    TermBind x Strict d@(VarDecl _ _ ty) rhs | not $ isFunctionType ty -> TermBind x NonStrict d rhs
    b -> b

thunkRecursions :: Term tyname name uni fun a -> Term tyname name uni fun a
thunkRecursions = \case
    -- See Note [Thunking recursions]
    t@(Let _ Rec _ _) -> t
        & over termSubterms thunkRecursions
        & over termBindings thunkBinding
    t -> t &
        over termSubterms thunkRecursions
