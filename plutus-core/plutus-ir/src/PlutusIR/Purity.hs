{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module PlutusIR.Purity
    ( isPure
    , firstEffectfulTerm
    , asBuiltinApp
    , isSaturated
    , BuiltinApp (..)
    , Arg (..)
    ) where

import PlutusIR

import Data.List.NonEmpty qualified as NE
import PlutusCore.Builtin

-- | An argument taken by a builtin: could be a term of a type.
data Arg tyname name uni fun a = TypeArg (Type tyname uni a) | TermArg (Term tyname name uni fun a)

-- | A (not necessarily saturated) builtin application,
-- consisting of the builtin and the arguments it has been applied to.
data BuiltinApp tyname name uni fun a = BuiltinApp fun [Arg tyname name uni fun a]

saturatesScheme ::  [Arg tyname name uni fun a] -> TypeScheme val args res -> Maybe Bool
-- We've passed enough arguments that the builtin will reduce.
-- Note that this also accepts over-applied builtins.
saturatesScheme _ TypeSchemeResult{}                     = Just True
-- Consume one argument
saturatesScheme (TermArg _ : args) (TypeSchemeArrow sch) = saturatesScheme args sch
saturatesScheme (TypeArg _ : args) (TypeSchemeAll _ sch) = saturatesScheme args sch
-- Under-applied, not saturated
saturatesScheme [] TypeSchemeArrow{}                     = Just False
saturatesScheme [] TypeSchemeAll{}                       = Just False
-- These cases are only possible in case we have an ill-typed builtin application,
-- so we can't give an answer.
saturatesScheme (TypeArg _ : _) TypeSchemeArrow{}        = Nothing
saturatesScheme (TermArg _ : _) TypeSchemeAll{}          = Nothing

-- | Is the given 'BuiltinApp' saturated?
-- Returns 'Nothing' if something is badly wrong and we can't tell.
isSaturated
    :: forall tyname name uni fun a
    . ToBuiltinMeaning uni fun
    => BuiltinVersion fun
    -> BuiltinApp tyname name uni fun a
    -> Maybe Bool
isSaturated ver (BuiltinApp fun args) =
    case toBuiltinMeaning @uni @fun @(Term TyName Name uni fun ()) ver fun of
        BuiltinMeaning sch _ _ -> saturatesScheme args sch

-- | View a 'Term' as a 'BuiltinApp' if possible.
asBuiltinApp :: Term tyname name uni fun a -> Maybe (BuiltinApp tyname name uni fun a)
asBuiltinApp = go []
    where
        go argsSoFar = \case
            Apply _ t arg  -> go (TermArg arg:argsSoFar) t
            TyInst _ t arg -> go (TypeArg arg:argsSoFar) t
            Builtin _ b    -> Just $ BuiltinApp b argsSoFar
            _              -> Nothing

{- Note [Purity, strictness, and variables]
Variables in PLC won't have effects: they can have something else substituted for them,
but those will be fully evaluated already.
However, in PIR we have non-strict variable bindings.
References to non-strict variables *can* have effects - after all,
they compile into an application.

So we need to take this into account in our purity calculation.
We require the user to tell us which variables are strict, this
must be *conservative* (i.e. if you don't know, it's non-strict).
-}

-- | Will evaluating this term have side effects (looping or error)?
-- This is slightly wider than the definition of a value, as
-- it includes applications that are known to be pure, as well as
-- things that can't be returned from the machine (as they'd be ill-scoped).
isPure ::
    ToBuiltinMeaning uni fun =>
    BuiltinVersion fun ->
    (name -> Strictness) ->
    Term tyname name uni fun a ->
    Bool
isPure ver varStrictness = go
    where
        go = \case
            -- See Note [Purity, strictness, and variables]
            Var _ n -> case varStrictness n of
                Strict    -> True
                NonStrict -> False
            -- These are syntactically values that won't reduce further
            LamAbs {} -> True
            TyAbs {} -> True
            Constant {} -> True
            IWrap _ _ _ t -> go t
            -- A non-recursive `Let` is pure if all bindings are pure and the body is pure.
            -- A recursive `Let` may loop, so we consider it non-pure.
            Let _ NonRec bs t -> all isPureBinding bs && go t
            -- A constructor is pure if all of its elements are pure
            Constr _ _ _ es -> all go es

            x | Just bapp@(BuiltinApp _ args) <- asBuiltinApp x ->
                -- Pure only if we can tell that the builtin application is not saturated
                maybe False not (isSaturated ver bapp)
                &&
                -- But all the arguments need to also be effect-free, since they will be evaluated
                -- when we evaluate the application.
                all (\case { TermArg arg -> go arg; TypeArg _ -> True }) args

            _ -> False

        isPureBinding = \case
            TermBind _ Strict _ rhs -> go rhs
            _                       -> True

{- |
Try to identify the first sub term which will be evaluated in the given term and
which could have an effect. 'Nothing' indicates that we don't know, this function
is conservative.
-}
firstEffectfulTerm :: Term tyname name uni fun a -> Maybe (Term tyname name uni fun a)
firstEffectfulTerm = goTerm
    where
      goTerm = \case
        Let _ NonRec bs b -> case goBindings (NE.toList bs) of
            Just t' -> Just t'
            Nothing -> goTerm b

        Apply _ l _ -> goTerm l
        TyInst _ t _ -> goTerm t
        IWrap _ _ _ t -> goTerm t
        Unwrap _ t -> goTerm t
        Constr _ _ _ [] -> Nothing
        Constr _ _ _ (t:_) -> goTerm t
        Case _ _ t _ -> goTerm t

        t@Var{} -> Just t
        t@Error{} -> Just t
        t@Builtin{} -> Just t

        -- Hard to know what gets evaluated first in a recursive let-binding,
        -- just give up and say nothing
        (Let _ Rec _ _) -> Nothing
        TyAbs{} -> Nothing
        LamAbs{} -> Nothing
        Constant{} -> Nothing

      goBindings :: [Binding tyname name uni fun a] -> Maybe (Term tyname name uni fun a)
      goBindings [] = Nothing
      goBindings (b:bs) = case b of
        -- Only strict term bindings can cause effects
        TermBind _ Strict _ rhs -> goTerm rhs
        _                       -> goBindings bs
