{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Float bindings inwards.
module PlutusIR.Transform.LetFloatIn (floatTerm) where

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name qualified as PLC
import PlutusIR
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.Purity
import PlutusIR.Transform.Rename ()

import Control.Lens hiding (Strict)
import Control.Monad.Extra (ifM)
import Control.Monad.Trans.Reader
import Data.Foldable (foldrM)
import Data.List.Extra qualified as List
import Data.List.NonEmpty.Extra (NonEmpty (..))
import Data.List.NonEmpty.Extra qualified as NonEmpty
import Data.Set (Set)
import Data.Set qualified as Set

{- Note [Float-in]

-------------------------------------------------------------------------------
1. Which bindings can be floated in?
-------------------------------------------------------------------------------

Strict bindings whose RHSs are impure should never be moved, since they can change the
semantics of the program. We can only move non-strict bindings or strict bindings
whose RHSs are pure.

We also need to be very careful about moving a strict binding whose RHS is not a work-free
(though pure). Consider a strict binding whose RHS is a pure, expensive application. If we
move it into, e.g., a lambda, its RHS may end up being evaluated more times. Although this
doesn't change the semantics of the program, it can make it much more expensive. For
simplicity, we do not move such bindings either.

In the rest of this Note, we may simply use "binding" to refer to either a non-strict
binding, or a strict binding whose RHS is work-free. Usually there's no need to distinguish
between these two, since `let x (nonstrict) = rhs` is essentially equivalent to
`let x (strict) = all a rhs`.

-------------------------------------------------------------------------------
2. The effect of floating in
-------------------------------------------------------------------------------

If we only float in bindings that are either non-strict, or whose RHSs is a work-free, then
why does that make a difference? Because such bindings are not completely free: when we
move a non-strict binding `let x (nonstrict) = rhs`, what we are really moving around is
`delay rhs`, lambda abstractions and lambda applications. None of them is free because
they incur CEK machine costs.

Here's a concrete example where floating a non-strict binding inwards saves cost:

let a (nonstrict) = rhs in if True then t else ..a..

Without floating `a` into the `else` branch, it is compiled into (in pseudo-UPLC)

[(\a -> if True then t else ..a..) (delay rhs)]

If we float `a` into the `else` branch, then it is compiled into

if True then t else [(\a -> ..a..) rhs]

Since the `else` branch is not taken, the former incurs additional `LamAbs`, `Apply`
and `Delay` steps when evaluated by the CEK machine. Note that `rhs` itself is
evaluated the same number of times (i.e., zero time) in both cases.

And floating a binding inwards can also increases cost. Here's an example:

let a (nonstrict) = rhs in let b (nonstrict) = a in b+b

Because `b` is non-strict and occurs twice in the body, floating the definition of `a` into
the RHS of `b` will incur one more of each of these steps: `Delay`, `LamAbs` and `Apply`.

-------------------------------------------------------------------------------
3. When can floating-in increase costs?
-------------------------------------------------------------------------------

Floating-in a binding can increase cost only if the binding is originally outside of `X`,
and is floated into `X`, and `X` satisfies both of the following conditions:

(1) `X` is a lambda abstraction, a type abstraction, or the RHS of a non-strict binding
(recall that the RHS of a non-strict binding is equivalent to a type abstraction).

(2) `X` is in the RHS of a (either strict or non-strict) binding whose LHS is used more than once.

Note the "only if" - the above are the necessary conditions, but not sufficient. Also note
that this is in the context of the float-in pass itself. Floating a binding in /can/ affect
ther subsequent optimizations in a negative way (e.g., inlining).

-------------------------------------------------------------------------------
4. Implementation of the float-in pass
-------------------------------------------------------------------------------

This float-in pass is a conservative optimization which tries to avoid increasing costs.
The implementation recurses into the top-level `Term` using the following context type:

data FloatInContext = FloatInContext
    { _ctxtInManyOccRhs :: Bool
    , _ctxtUsages       :: Usages.Usages
    }

`ctxtUsages` is the usage counts of variables, and `ctxtInManyOccRhs` is initially `False`.
`ctxtInManyOccRhs` is set to `True` if we descend into:

(1) The RHS of a binding whose LHS is used more than once
(2) The argument of an application, unless the function is a LamAbs whose bound variable
is used at most once, or a Builtin.

The value of `ctxtInManyOccRhs` is used as follows:

(1) When `ctxtInManyOccRhs = False`, we avoid descending into the RHS of a non-strict binding
whose LHS is used more than once, and we descend in all other cases;
(2) When `ctxtInManyOccRhs = True`, we additionally avoid descending into `LamAbs` or `TyAbs`.

-}

type Uniques = Set PLC.TermUnique

data FloatInContext = FloatInContext
    { _ctxtInManyOccRhs :: Bool
    -- ^ Whether we are in the RHS of a binding whose LHS is used more than once.
    -- See Note [Float-in] #4
    , _ctxtUsages       :: Usages.Usages
    }

makeLenses ''FloatInContext

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
floatTerm ver t0 = do
    t1 <- PLC.rename t0
    pure . fmap fst $ floatTermInner (Usages.termUsages t1) t1
  where
    floatTermInner ::
        Usages.Usages ->
        Term tyname name uni fun a ->
        Term tyname name uni fun (a, Uniques)
    floatTermInner usgs = go
      where
        -- Float bindings in the given `Term` inwards, and annotate each term with the set of
        -- used term `Unique`s in the `Term`.
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
                    -- e.g. let x = 1; y = x in ... y ...
                    -- we want to float y in first otherwise it will block us from floating in x
                    runReader
                        (foldrM (floatInBinding ver a) body bs)
                        (FloatInContext False usgs)
            Let a Rec bs0 body0 ->
                -- Currently we don't move recursive bindings, so we simply descend into the body.
                let bs = goBinding <$> bs0
                    body = go body0
                    us = Set.union (termUniqs body) (foldMap bindingUniqs bs)
                 in Let (a, us) Rec bs body
            Var a n -> Var (a, Set.singleton (n ^. PLC.unique)) n
            Constant{} -> (,mempty) <$> t
            Builtin{} -> (,mempty) <$> t
            Error{} -> noUniq t

        -- Float bindings in the given `Binding` inwards, and calculate the set of
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

-- See Note [Float-in] #1
floatable ::
    PLC.ToBuiltinMeaning uni fun =>
    PLC.BuiltinVersion fun ->
    Binding tyname name uni fun a ->
    Bool
floatable ver = \case
    TermBind _a Strict _var rhs     -> isEssentiallyWorkFree ver rhs
    TermBind _a NonStrict _var _rhs -> True
    -- We currently don't move type and datatype bindings.
    TypeBind{}                      -> False
    DatatypeBind{}                  -> False

{- | Whether evaluating a given `Term` is essentially work-free (barring the CEK machine overhead).

 See Note [Float-in] #1
-}
isEssentiallyWorkFree ::
    PLC.ToBuiltinMeaning uni fun => PLC.BuiltinVersion fun -> Term tyname name uni fun a -> Bool
isEssentiallyWorkFree ver = go
  where
    go = \case
        LamAbs{} -> True
        TyAbs{} -> True
        Constant{} -> True
        x
            | Just bapp@(BuiltinApp _ args) <- asBuiltinApp x ->
                maybe False not (isSaturated ver bapp)
                    && all (\case TermArg arg -> go arg; TypeArg _ -> True) args
        _ -> False

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
    Reader FloatInContext (Term tyname name uni fun (a, Uniques))
floatInBinding ver letAnn = \b ->
    if floatable ver b
        then go b
        else \body ->
            let us = Set.union (termUniqs body) (bindingUniqs b)
             in pure $ Let (letAnn, us) NonRec (pure b) body
  where
    go ::
        Binding tyname name uni fun (a, Uniques) ->
        Term tyname name uni fun (a, Uniques) ->
        Reader FloatInContext (Term tyname name uni fun (a, Uniques))
    go b !body = case b of
        TermBind (_, usBind) _s var _rhs -> case body of
            Apply (a, usBody) fun arg
                | (var ^. PLC.unique) `Set.notMember` termUniqs fun -> do
                    -- `fun` does not mention `var`, so we can place the binding inside `arg`.
                    -- See Note [Float-in] #3
                    usgs <- asks _ctxtUsages
                    let inManyOccRhs = case fun of
                            LamAbs _ name _ _ ->
                                Usages.getUsageCount name usgs > 1
                            Builtin{} -> False
                            -- We need to be conservative here, this could be something 
                            -- that computes to a function that uses its argument repeatedly.
                            _ -> True
                    Apply (a, Set.union usBind usBody) fun
                        <$> local (over ctxtInManyOccRhs (|| inManyOccRhs)) (go b arg)
                | (var ^. PLC.unique) `Set.notMember` termUniqs arg ->
                    -- `arg` does not mention `var`, so we can place the binding inside `fun`.
                    Apply (a, Set.union usBind usBody) <$> go b fun <*> pure arg
            LamAbs (a, usBody) n ty lamAbsBody ->
                -- We float into lambdas only if `_ctxtInManyOccRhs = False`.
                -- See Note [Float-in] #3
                ifM
                    (asks _ctxtInManyOccRhs)
                    giveup
                    (LamAbs (a, Set.union usBind usBody) n ty <$> go b lamAbsBody)
            TyAbs (a, usBody) n k tyAbsBody ->
                -- We float into type abstractions only if `_ctxtInManyOccRhs = False`.
                -- See Note [Float-in] #3
                ifM
                    (asks _ctxtInManyOccRhs)
                    giveup
                    (TyAbs (a, Set.union usBind usBody) n k <$> go b tyAbsBody)
            TyInst (a, usBody) tyInstBody ty ->
                -- A term binding can always be placed inside the body a `TyInst` because the
                -- type cannot mention the bound variable
                TyInst (a, Set.union usBind usBody) <$> go b tyInstBody <*> pure ty
            Let (a, usBody) NonRec bs letBody
                -- The binding can be placed inside a `Let`, if the right hand sides of the
                -- bindings of the `Let` do not mention `var`.
                | (var ^. PLC.unique) `Set.notMember` foldMap bindingUniqs bs ->
                    Let (a, Set.union usBind usBody) NonRec bs <$> go b letBody
                | (var ^. PLC.unique) `Set.notMember` termUniqs letBody -> do
                    splitBindings (var ^. PLC.unique) (NonEmpty.toList bs) >>= \case
                        Just
                            ( before
                                , TermBind (a', usBind') s' var' rhs'
                                , after
                                , inManyOccRhs
                                ) -> do
                                -- `letBody` does not mention `var`, and there is exactly one
                                -- RHS in `bs` that mentions `var`, so we can place `b`
                                -- inside one of the RHSs in `bs`.
                                b'' <-
                                    TermBind (a', Set.union usBind usBind') s' var'
                                        <$> local
                                            (over ctxtInManyOccRhs (|| inManyOccRhs))
                                            (go b rhs')
                                let bs' = NonEmpty.appendr before (b'' :| after)
                                pure $ Let (a, Set.union usBind usBody) NonRec bs' letBody
                        _ -> giveup
            IWrap (a, usBody) ty1 ty2 iwrapBody ->
                -- A binding can always be placed inside an `IWrap`.
                IWrap (a, Set.union usBind usBody) ty1 ty2 <$> go b iwrapBody
            Unwrap (a, usBody) unwrapBody ->
                -- A binding can always be placed inside an `Unwrap`.
                Unwrap (a, Set.union usBind usBody) <$> go b unwrapBody
            _ -> giveup
        -- TODO: implement float-in for type and datatype bindings.
        _ -> giveup
      where
        giveup =
            let us = Set.union (termUniqs body) (bindingUniqs b)
             in pure $ Let (letAnn, us) NonRec (pure b) body

{- | Split the given list of bindings, if possible.
 If the input contains exactly one binding @b@ that mentions the given `PLC.TermUnique`,
 return @Just (before_b, b, after_b)@.
 Otherwise, return `Nothing`.
-}
splitBindings ::
    PLC.HasUnique name PLC.TermUnique =>
    PLC.TermUnique ->
    [Binding tyname name uni fun (a, Uniques)] ->
    Reader
        FloatInContext
        ( Maybe
            ( [Binding tyname name uni fun (a, Uniques)]
            , Binding tyname name uni fun (a, Uniques)
            , [Binding tyname name uni fun (a, Uniques)]
            , Bool
            -- \^ Whether the chosen binding occurs more than once.
            )
        )
splitBindings u bs = case is of
    [(TermBind _ Strict var _, i)] -> do
        usgs <- asks _ctxtUsages
        pure $
            Just
                ( take i bs
                , bs !! i
                , drop (i + 1) bs
                , Usages.getUsageCount var usgs > 1
                )
    [(TermBind _ NonStrict var _, i)] -> do
        ctxt <- ask
        pure $
            if (ctxt ^. ctxtInManyOccRhs)
                -- Descending into a non-strict binding whose LHS is used more than once
                -- should be avoided, regardless of `ctxtInManyOccRhs`.
                -- See Note [Float-in] #3
                || Usages.getUsageCount var (ctxt ^. ctxtUsages) > 1
                then Nothing
                else Just (take i bs, bs !! i, drop (i + 1) bs, True)
    _ -> pure Nothing
  where
    is = List.filter containsUniq (bs `zip` [0 ..])
    containsUniq = \case
        (TermBind _ _ _ rhs, _) -> u `Set.member` termUniqs rhs
        _                       -> False
