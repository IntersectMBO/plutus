-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
-- | Implements a PIR-to-PIR transformation that makes all recursive term definitions
-- compilable to PLC. See Note [Thunking recursions] for details.
module PlutusIR.Transform.ThunkRecursions (thunkRecursions) where

import Control.Lens (transformOf)
import Data.List.NonEmpty (partition)
import Data.Maybe (mapMaybe)
import PlutusCore.Builtin
import PlutusIR
import PlutusIR.MkPir (mkLet, mkVar)
import PlutusIR.Purity (isPure)

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

We *do* still need a strict adapter binding, so that any effects of the RHS of the binding
will still get triggered, e.g.

    let rec x = error
            y = x
    in x

becomes

    let rec x = \() -> error
            y = x ()
    in let x = x () -- error gets triggered here
    in x

To do this without having to do lots of substitutions, we use the same identifier for the
recursive binding and the adapter binding, so this pass destroys global uniqueness.

At the moment we only do this for bindings whose RHS is potentially impure, although in
principle it could be an improvement in other cases because it would allow using the faster
strict binding in the body. Unclear.
-}

isFunctionType :: Type tyname uni a -> Bool
isFunctionType = \case
    TyFun {} -> True
    _        -> False

strictNonFunctionBinding :: Binding tyname name uni fun a -> Bool
strictNonFunctionBinding = \case
    TermBind _ Strict (VarDecl _ _ ty) _ | not $ isFunctionType ty -> True
    _                                                              -> False

nonStrictify :: Binding tyname name uni fun a -> Binding tyname name uni fun a
nonStrictify = \case
    TermBind x _ d rhs -> TermBind x NonStrict d rhs
    b                  -> b

mkStrictifyingBinding
    :: ToBuiltinMeaning uni fun
    => BuiltinSemanticsVariant fun
    -> Binding tyname name uni fun a
    -> Maybe (Binding tyname name uni fun a)
mkStrictifyingBinding semvar = \case
    -- Only need to strictify if the previous binding was not definitely pure
    -- Also, we're reusing the same variable here, see Note [Thunking recursions]
    TermBind x _ d rhs | not (isPure semvar (const NonStrict) rhs) -> Just $ TermBind x Strict d (mkVar x d)
    _                                                           -> Nothing

thunkRecursionsStep
    :: ToBuiltinMeaning uni fun
    => BuiltinSemanticsVariant fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
thunkRecursionsStep semvar (Let a Rec bs t) =
    -- See Note [Thunking recursions]
    let (toThunk, noThunk) = partition strictNonFunctionBinding bs
        newBindings = fmap nonStrictify toThunk ++ noThunk
        strictifiers = mapMaybe (mkStrictifyingBinding semvar) toThunk
    in mkLet a Rec newBindings $ mkLet a NonRec strictifiers t
thunkRecursionsStep _ t = t

-- | Thunk recursions to turn recusive values of non-function type into recursive values of function type,
-- so we can compile them.
--
-- Note: this pass breaks global uniqueness!
thunkRecursions
    :: ToBuiltinMeaning uni fun
    => BuiltinSemanticsVariant fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
thunkRecursions = transformOf termSubterms . thunkRecursionsStep
