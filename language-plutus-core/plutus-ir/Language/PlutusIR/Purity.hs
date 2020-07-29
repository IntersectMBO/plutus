{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Language.PlutusIR.Purity (isPure) where

import           Language.PlutusIR

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Constant.Name
import qualified Language.PlutusCore as PLC

import           Data.Proxy
import qualified Data.Map as Map

-- | An argument taken by a builtin: could be a term of a type.
data Arg tyname name uni a = TypeArg (Type tyname uni a) | TermArg (Term tyname name uni a)

-- | A (not necessarily saturated) builtin application, consisting of the builtin and the arguments it has been applied to.
data BuiltinApp tyname name uni a = BuiltinApp (PLC.Builtin a) [Arg tyname name uni a]

saturatesScheme ::  [Arg tyname name uni a] -> TypeScheme term args res -> Bool
saturatesScheme [] TypeSchemeResult{} = True
saturatesScheme (TermArg _ : args) (TypeSchemeArrow _ sch) = saturatesScheme args sch
saturatesScheme (TypeArg _ : args) (TypeSchemeAllType _ k) = saturatesScheme args (k Proxy)
saturatesScheme _ _ = False

-- | Is the given 'BuiltinApp' saturated?
isSaturated
    :: forall tyname name uni a term
    . (HasConstantIn uni term, PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni)
    => DynamicBuiltinNameMeanings term
    -> BuiltinApp tyname name uni a
    -> Bool
isSaturated (DynamicBuiltinNameMeanings means) (BuiltinApp b args) = case b of
    PLC.BuiltinName _ bn -> withTypedBuiltinName @uni @term bn $ \(TypedBuiltinName _ sch) -> saturatesScheme args sch
    PLC.DynBuiltinName _ bn -> case Map.lookup bn means of
        Just (DynamicBuiltinNameMeaning sch _ _) -> saturatesScheme args sch
        Nothing -> False

-- | View a 'Term' as a 'BuiltinApp' if possible.
asBuiltinApp :: Term tyname name uni a -> Maybe (BuiltinApp tyname name uni a)
asBuiltinApp = go []
    where
        go argsSoFar = \case
            Apply _ t arg -> go (TermArg arg:argsSoFar) t
            TyInst _ t arg -> go (TypeArg arg:argsSoFar) t
            Builtin _ b -> Just $ BuiltinApp b argsSoFar
            _ -> Nothing

{- Note [Purity, strictness, and variables]
Variables in PLC won't have effects: they can have something else substituted for them, but those will be fully evaluated already.
However, in PIR we have non-strict variable bindings. References to non-strict variables *can* have effects - after all,
they compile into an application.

So we need to take this into account in our purity calculation. We require the user to tell us which variables are strict, this
must be *conservative* (i.e. if you don't know, it's non-strict).
-}

-- | Will evaluating this term have side effects (looping or error)?. This is slightly wider than the definition of a value, as
-- it includes things that can't be returned from the machine (as they'd be ill-scoped).
isPure
    :: (HasConstantIn uni term, PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni)
    => DynamicBuiltinNameMeanings term -> (name -> Strictness) -> Term tyname name uni a -> Bool
isPure means varStrictness = go
    where
        go = \case
            -- See Note [Purity, strictness, and variables]
            Var _ n -> case varStrictness n of
                Strict -> True
                NonStrict -> False
            -- These are syntactically values that won't reduce further
            LamAbs {} -> True
            TyAbs {} -> True
            Constant {} -> True
            IWrap _ _ _ t -> go t

            -- "Stuck" builtin applications won't compute, so won't have effects
            x | Just bapp@(BuiltinApp _ args) <- asBuiltinApp x ->
                not $ isSaturated means bapp
                &&
                -- But all the arguments need to also be effect-free, since they will be evaluated
                -- when we evaluate the application.
                all (\case { TermArg arg -> go arg; TypeArg _ -> True }) args

            _ -> False
