-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
-- | Implements a PIR-to-PIR transformation that makes all recursive term definitions
-- compilable to PLC. See Note [Thunking recursions] for details.
module PlutusIR.Transform.ThunkRecursions (thunkRecursions) where

import PlutusCore.Builtin
import PlutusCore.Name qualified as PLC
import PlutusIR
import PlutusIR.Analysis.Builtins
import PlutusIR.Analysis.VarInfo
import PlutusIR.MkPir (mkLet, mkVar)
import PlutusIR.Purity

import Control.Lens hiding (Strict)
import Data.List.NonEmpty qualified as NE

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

To make sure the effects order does not change, we must also apply this
transformation to all sibling bindings which are effectful, although they aren't problematic.
We place all strict adapters (for both problematic and non problematic bindings)
in their original ordering to preserve the order of effects.

We could, while keeping the thunkification in place, skip the strictification for those
problematic, pure-strict bindings. These would essentially safely alter their original strictness.
We opt not to, because it is not clear if it would be a benefit (this pass is not supposed to do
any kind of strictness analysis).
-}

isTyFun :: Type tyname uni a -> Bool
isTyFun = \case
    TyFun {} -> True
    _        -> False

nonStrictifyB :: Binding tyname name uni fun a -> Binding tyname name uni fun a
nonStrictifyB = \case
    TermBind x _ d rhs -> TermBind x NonStrict d rhs
    b                  -> b

-- Out of a binding `(vardecl x = rhs)`, make a "strictifier" binding: `(strict vardecl x = x)`
mkStrictifierB :: Binding tyname name uni fun a -> Binding tyname name uni fun a
mkStrictifierB = \case
    TermBind x _ d _ -> TermBind x Strict d (mkVar x d)
    b                -> b

thunkRecursionsStep
    :: forall tyname name uni fun a
    . (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique)
    => BuiltinsInfo uni fun
    -> VarsInfo tyname name
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
thunkRecursionsStep binfo vinfo = \case
 -- only apply the transformation if there is at least 1 problematic binding in a letrec group
  Let a Rec bs t | any isProblematic bs ->
    -- See Note [Thunking recursions]
    let (toNonStrictify, rest) = NE.partition needsNonStrictify bs
        -- MAYBE: use some prism/traversal to keep the original arrangement of the let group
        -- this is not a semantic problem, but just a stylistic/debugging issue where the original
        -- let-group will have reordered the (lazified) bindings
        editedLet = mkLet a Rec $ fmap nonStrictifyB toNonStrictify ++ rest
        -- We insert strictifiers for all previously thunkified
        strictifiers = mkStrictifierB <$> toNonStrictify
        extraLet = mkLet a NonRec strictifiers
    in editedLet $ extraLet t
  t -> t
  where
    isStrictEffectful :: Binding tyname name uni fun a -> Bool
    isStrictEffectful = \case
        TermBind _ Strict _ rhs -> not $ isPure binfo vinfo rhs
        _                       -> False

    needsNonStrictify :: Binding tyname name uni fun a -> Bool
    needsNonStrictify b = isProblematic b || isStrictEffectful b

-- | The problematic bindings are those that are strict and their type is not a TyFun
isProblematic :: Binding tyname name uni fun a -> Bool
isProblematic = \case
    TermBind _ Strict (VarDecl _ _ ty) _ -> not $ isTyFun ty
    _                                    -> False

-- | Thunk recursions to turn recusive values of non-function type into recursive values of function type,
-- so we can compile them.
--
-- Note: this pass breaks global uniqueness!
thunkRecursions
    :: (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
    => BuiltinsInfo uni fun
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
thunkRecursions binfo t = transformOf termSubterms (thunkRecursionsStep binfo (termVarInfo t)) t
