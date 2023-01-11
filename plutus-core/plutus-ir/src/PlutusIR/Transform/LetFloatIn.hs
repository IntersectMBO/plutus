{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE ViewPatterns      #-}

{- | Float bindings inwards.

This usually reduces the evaluation cost of the program, but can sometimes lead to
increased cost. However, the latter is uncommon and the additional cost is almost
always small compared to the total cost.
-}
module PlutusIR.Transform.LetFloatIn (floatTerm) where

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name qualified as PLC
import PlutusIR
import PlutusIR.Purity (isPure)
import PlutusIR.Transform.Rename ()

import Control.Lens hiding (Strict)
import Control.Monad ((<=<))
import Data.Set (Set)
import Data.Set qualified as Set

{- Note [Which bindings can be floated inwards?]

Moving a lazy binding obviously doesn't change the semantics of the program, since the RHS of
a lazy binding is always evaluated whenever needed, and only evaluated when needed, regardless
of where the binding is placed. Lazy bindings therefore can be floated inwards.

Why, one might ask, does floating lazy bindings inwards save cost, if the RHS is always
evaluated the same number of times? Because when we move a lazy binding `let x (nonstrict) = rhs`,
what we are really moving around is `delay rhs` and lambda applications, and neither
`delay rhs` nor lambda application is free - they incur additional `Delay`, `LamAbs`
and `Apply` steps in the CEK machine. Thus cost can be saved by floating bindings into
unevaluated branches.

The same applies to strict bindings, because `let x (nonstrict) = rhs` is really nothing
but `let x (strict) = forall a. rhs`.

Here's a concrete example:

let a (nonstrict) = rhs in if True then t else ..a..

Without floating `a` into the `else` branch, it is compiled into (in pseudo-UPLC)

[(\a -> if True then t else ..a..) (delay rhs)]

If we float `a` into the `else` branch, then it is compiled into

if True then t else [(\a -> ..a..) rhs]

Since the `else` branch is not taken, the former incurs additional `LamAbs`, `Apply`
and `Delay` steps when evaluated by the CEK machine. Note that `rhs` itself is
evaluated the same number of times (i.e., zero time) in both cases.

We are using pseudo-UPLC here for better readibility. In the actual UPLC, if-then-else
is compiled into Scott-encoded Booleans (basically a bunch of lambdas), but the same
reasoning remains.

Moving a strict binding can change the semantics of the program. For example, if `rhs`
evaluates to bottom, then

let a (strict) = rhs in if True then t else ..a..

evaluates to bottom, since `rhs` is evaluated immediately. But if we float `rhs` into
the `else` branch, then `rhs` is no longer evaluated. Therefore we only move a strict
binding if its RHS is guaranteed to be effect-free.

Furthermore, moving a strict binding is much more likely to increase the cost of the
program. Floating a strict binding into the RHS of another binding, or into the
argument of an application, can cause its RHS to be evaluated multiple times.
See Note [Where can a binding be floated into?] for examples. We therefore only move
strict bindings whose RHS is trivial to evaluated (such as a variable or a
lambda abstraction). Since being trivial to evaluate implies being effect-free, we
only need to check the former.
-}

{- Note [Where can a binding be floated into?]

TL;DR: Floating a binding into the RHS of another binding, the argument of an application,
or a (term or type) lambda abstraction, can all lead to increased costs, even if
we only float lazy bindings, and strict bindings that are trivial to evaluate.

The reason for the cost increase is the same as why floating bindings inwards can
save cost: when we are moving a bind `let x (nonstrict) = rhs`, what is really
being moved around is `delay rhs` and lambda applications, which are not free.

We choose to avoid floating bindings into the RHS of another binding. By doing so,
floating bindings into lambda abstractions can no longer increase costs. On the other
hand, we _do_ float bindings into arguments of applications. This may lead to increased
costs, but when it occurs, the increase is almost always small compared to the total
cost of the program.

Next we explain the above statements in details.

==== Floating a binding into the RHS of another binding ====

Here's an example where floating a binding into the RHS of another binding leads to
increased cost due to the CEK machine taking more steps to evaluate the program:

let x (nonstrict) = rhs_x
 in let y = x+x in y+y

Without floating, it is compiled into

[(\x -> [(\y -> y+y) (delay (x+x))] (delay rhs_x)]

and evaluating this program involves two `Delay` steps, one for each `delay`.

If we float `x` into the RHS of `y`, it will be compiled into

[(\y -> y+y) (delay [(\x -> x+x) (delay rhs_x)])]

and evaluating this program involves three `Delay` steps, one for the first `delay` and
two for the second `delay`. Note that the second `delay` is inside the first `delay`.

Again we are using pseudo-UPLC here for better readability, e.g., we omitted such things
as `force`. The number of `Force` steps are the same with or without floating in,
which follows from the fact that `rhs_x` is always evaluated the same number of times
however we do the floating.

==== Floating a binding into the argument of an application ====

Since floating a binding into the RHS of another binding can lead to increased costs,
it follows that floating a binding into the argument of an application can as well,
because `let x (nonstrict) = rhs in body` is the same as `(\x -> force body) (delay rhs)`,
and `let x (strict) = rhs in body` is the same as `(\x -> body) rhs`.

However, we _do_ float bindings into arguments due to the following considerations:

  - Due to transformations done by GHC, it is unlikely that the plugin gets expressions
    like `(\x -> body) rhs`. Much more often, it is something like
    `let fun = \x -> body in let arg = rhs in fun arg`.
  - Test results show that not floating bindings into arguments negates almost all
    benefits of floating bindings inwards.
  - The additional cost is almost always small compared to the total cost. As explained
    above, the additional cost is caused by moving `delay rhs` (in the case of lazy bindings)
    and lambda applications around. Intuitively, Although these are not free, they are
    almost always much cheaper than the cost of "doing the real work".

==== Floating a binding into a (term or type) lambda abstraction ====

It is easy to see that floating a binding into a lambda abstraction can increase cost,
if the lambda abstraction is applied multiple times. This is also the reason why
GHC avoids floating bindings into lambda abstractions. But note that if a lambda
abstraction is applied multiple times, it can only be because it is in the RHS of
a binding. Since we already avoid floating a binding into the RHS of another binding,
we do not need to treat lambda abstractions specially, i.e., we can safely float
bindings into lambda abstractions.

It is also worth mentioning that in GHC Core, lazy bindings are thunks, which are
evaluated at most once. Therefore, for GHC, floating bindings into lambda abstractions
can lead to unbounded cost increases, since the RHS itself, which can be arbitrarily
expensive, can be evaluated more times. This is not the case for PIR.
-}

type Uniques = Set PLC.TermUnique

-- | Float bindings in the given `Term` inwards.
floatTerm ::
    forall m tyname name uni fun a.
    ( PLC.HasUnique name PLC.TermUnique
    , PLC.HasUnique tyname PLC.TypeUnique
    , PLC.ToBuiltinMeaning uni fun
    , PLC.MonadQuote m
    ) =>
    PLC.BuiltinVersion fun ->
    Term tyname name uni fun a ->
    m (Term tyname name uni fun a)
floatTerm ver = pure . fmap fst . go <=< PLC.rename
  where
    -- \| Float bindings in the given `Term` inwards, and calculate the set of
    -- variable `Unique`s in the result `Term`.
    go ::
        Term tyname name uni fun a ->
        Term tyname name uni fun (a, Uniques)
    go t = case t of
        Apply a fun0 arg0 ->
            let fun = go fun0
                arg = go arg0
                us = termUniqs fun `Set.union` termUniqs arg
             in Apply (a, us) fun arg
        LamAbs a n ty body0 ->
            let body = go body0
             in LamAbs (a, termUniqs body) n (noUniq ty) body
        TyAbs a n k body0 ->
            let body = go body0
             in TyAbs (a, termUniqs body) n (noUniq k) body
        TyInst a body0 ty ->
            let body = go body0
             in TyInst (a, termUniqs body) body (noUniq ty)
        IWrap a ty1 ty2 body0 ->
            let body = go body0
             in IWrap (a, termUniqs body) (noUniq ty1) (noUniq ty2) body
        Unwrap a body0 ->
            let body = go body0
             in Unwrap (a, termUniqs body) body
        Let a NonRec bs0 body0 ->
            let bs = goBinding <$> bs0
                body = go body0
             in -- The bindings in `bs` should be processed from right to left, since
                -- a binding may depend on another binding to its left.
                foldr (floatInBinding ver a) body bs
        Let a Rec bs0 body0 ->
            -- Currently we don't move recursive bindings, so we simply descend into the body.
            let bs = goBinding <$> bs0
                body = go body0
                us = Set.union (termUniqs body) (foldMap bindingUniqs bs)
             in Let (a, us) Rec bs body
        Var a n -> Var (a, Set.singleton (n ^. PLC.unique)) n
        Constant{} -> (,mempty) <$> t
        Builtin{} -> (,mempty) <$> t
        Error{} -> (,mempty) <$> t

    -- \| Float bindings in the given `Binding` inwards, and calculate the set of
    -- variable `Unique`s in the result `Binding`.
    goBinding ::
        Binding tyname name uni fun a ->
        Binding tyname name uni fun (a, Uniques)
    goBinding = \case
        TermBind a s var rhs ->
            let rhs' = go rhs
             in TermBind (a, termUniqs rhs') s (noUniq var) rhs'
        other -> noUniq other

termUniqs :: Term tyname name uni fun (a, Uniques) -> Uniques
termUniqs = snd . termAnn

-- | The result includes both the `Unique` of the bound var and the `Unique`s in the RHS.
bindingUniqs ::
    PLC.HasUnique name PLC.TermUnique =>
    Binding tyname name uni fun (a, Uniques) ->
    Uniques
bindingUniqs b = Set.union (snd (bindingAnn b)) $ case b of
    TermBind _a _s var _rhs -> Set.singleton $ var ^. PLC.varDeclName . PLC.unique
    _                       -> mempty

noUniq :: Functor f => f a -> f (a, Uniques)
noUniq = fmap (,mempty)

-- See Note [Which bindings can be floated inwards?]
floatable ::
    PLC.ToBuiltinMeaning uni fun =>
    PLC.BuiltinVersion fun ->
    Binding tyname name uni fun a ->
    Bool
floatable ver = \case
    TermBind _a Strict _var rhs     -> isPure ver (const NonStrict) rhs
    TermBind _a NonStrict _var _rhs -> True
    -- We currently don't move type and datatype bindings.
    TypeBind{}                      -> False
    DatatypeBind{}                  -> False

{- | Given a `Term` and a `Binding`, determine whether the `Binding` can be
 placed somewhere inside the `Term`.

 If yes, return the result `Term`. Otherwise, return a `Let` constructed from
 the given `Binding` and `Term`.
-}
floatInBinding ::
    forall tyname name uni fun a.
    ( PLC.HasUnique name PLC.TermUnique
    , PLC.ToBuiltinMeaning uni fun
    ) =>
    PLC.BuiltinVersion fun ->
    -- | Annotation to be attached to the constructed `Let`.
    a ->
    Binding tyname name uni fun (a, Uniques) ->
    Term tyname name uni fun (a, Uniques) ->
    Term tyname name uni fun (a, Uniques)
floatInBinding ver letAnn = \b ->
    if floatable ver b
        then go b
        else \body ->
            let us = Set.union (termUniqs body) (bindingUniqs b)
             in Let (letAnn, us) NonRec (pure b) body
  where
    go ::
        Binding tyname name uni fun (a, Uniques) ->
        Term tyname name uni fun (a, Uniques) ->
        Term tyname name uni fun (a, Uniques)
    go b !body = case b of
        TermBind (_, usBind) _s var _rhs -> case body of
            Apply (a, usBody) fun arg
                | (var ^. PLC.unique) `Set.notMember` termUniqs fun ->
                    -- `fun` does not mention `var`, so we can place the binding inside `arg`.
                    -- See Note [Where can a binding be floated into?].
                    Apply (a, Set.union usBind usBody) fun (go b arg)
                | (var ^. PLC.unique) `Set.notMember` termUniqs arg ->
                    -- `arg` does not mention `var`, so we can place the binding inside `fun`.
                    Apply (a, Set.union usBind usBody) (go b fun) arg
            LamAbs (a, usBody) n ty lamAbsBody ->
                -- A lazy binding, or a strict binding whose RHS is pure, can always
                -- be placed inside a `LamAbs`.
                -- See Note [Where can a binding be floated into?].
                LamAbs (a, Set.union usBind usBody) n ty (go b lamAbsBody)
            TyAbs (a, usBody) n k tyAbsBody ->
                -- A lazy binding, or a strict binding whose RHS is pure, can always
                -- be placed inside a `TyAbs`.
                -- See Note [Where can a binding be floated into?].
                TyAbs (a, Set.union usBind usBody) n k (go b tyAbsBody)
            TyInst (a, usBody) tyInstBody ty ->
                -- A term binding can always be placed inside the body a `TyInst` because the
                -- type cannot mention the bound variable
                TyInst (a, Set.union usBind usBody) (go b tyInstBody) ty
            Let (a, usBody) r bs letBody
                -- The binding can be placed inside a `Let`, if the right hand sides of the
                -- bindings of the `Let` do not mention `var`.
                --
                -- Note that we do *not* float the binding into one of the bindings here.
                -- See Note [Where can a binding be floated into?]
                | (var ^. PLC.unique) `Set.notMember` foldMap bindingUniqs bs ->
                    Let (a, Set.union usBind usBody) r bs (go b letBody)
            IWrap (a, usBody) ty1 ty2 iwrapBody ->
                -- A binding can always be placed inside an `IWrap`.
                IWrap (a, Set.union usBind usBody) ty1 ty2 (go b iwrapBody)
            Unwrap (a, usBody) unwrapBody ->
                -- A binding can always be placed inside an `Unwrap`.
                Unwrap (a, Set.union usBind usBody) (go b unwrapBody)
            _ ->
                let us = Set.union (termUniqs body) (bindingUniqs b)
                 in Let (letAnn, us) NonRec (pure b) body
        _ ->
            let us = Set.union (termUniqs body) (bindingUniqs b)
             in Let (letAnn, us) NonRec (pure b) body
