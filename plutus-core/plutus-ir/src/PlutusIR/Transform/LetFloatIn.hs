{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE ViewPatterns      #-}

{- | Float bindings inwards. A binding can be floated if it is a lazy binding, or
 a strict binding whose RHS is a value. Doing so does not have much impact on the
 program size since it simply moves bindings around without changing the number
 of bindings, but it may lead to more efficient evaluation.

 Unlike the float-in in GHC, we /can/ float bindings into lambda abstractions,
 because doing so cannot duplicate work. Therefore we simply float a binding
 inwards to the deepest possible position.

 We avoid moving a strict binding whose RHS is not a value, because doing so
 may either change the semantics (if the RHS has effects) or duplicate work
 (if it is floated into a lambda abstraction).

 Floating inwards is done in a single pass. The subterms are processed bottom-up,
 during which we keep track of the set of variable @Unique@s within each subterm.
 The time complexity is linear wrt AST size (strictly speaking it is /O(n*log n)/
 where the /log n/ comes from `Set` operations).

 Currently we only move non-recursive term bindings. In the future we should also
 implement float-in for other kinds of bindings.
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
    -- | Float bindings in the given `Term` inwards, and calculate the set of
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

    -- | Float bindings in the given `Binding` inwards, and calculate the set of
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
floatInBinding ver letAnn = go
  where
    go ::
        Binding tyname name uni fun (a, Uniques) ->
        Term tyname name uni fun (a, Uniques) ->
        Term tyname name uni fun (a, Uniques)
    go b !body = case b of
        TermBind _a Strict _var rhs
            -- A strict binding whose RHS is not pure cannot be moved.
            | not (isPure ver (const NonStrict) rhs) ->
                let us = Set.union (termUniqs body) (bindingUniqs b)
                 in Let (letAnn, us) NonRec (pure b) body
        TermBind (_, usBind) _strictness var _rhs -> case body of
            Apply (a, usBody) fun arg
                | (var ^. PLC.unique) `Set.notMember` termUniqs fun ->
                    -- `fun` does not mention `var`, so we can place the binding inside `arg`.
                    Apply (a, Set.union usBind usBody) fun (go b arg)
                | (var ^. PLC.unique) `Set.notMember` termUniqs arg ->
                    -- `arg` does not mention `var`, so we can place the binding inside `fun`.
                    Apply (a, Set.union usBind usBody) (go b fun) arg
            LamAbs (a, usBody) n ty lamAbsBody ->
                -- A binding can always be placed inside a `LamAbs`.
                LamAbs (a, Set.union usBind usBody) n ty (go b lamAbsBody)
            TyAbs (a, usBody) n k tyAbsBody ->
                -- A binding can always be placed inside a `TyAbs`.
                TyAbs (a, Set.union usBind usBody) n k (go b tyAbsBody)
            TyInst (a, usBody) tyInstBody ty ->
                -- A term binding can always be placed inside the body a `TyInst` because the
                -- type cannot mention the bound variable
                TyInst (a, Set.union usBind usBody) (go b tyInstBody) ty
            Let (a, usBody) r bs letBody
                -- The binding can be placed inside a `Let`, if the right hand sides of the
                -- bindings of the `Let` do not mention `var`.
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
