{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module PlutusIR.Purity
    ( isPure
    , isSaturated
    , isWorkFree
    , EvalOrder
    , unEvalOrder
    , EvalTerm (..)
    , Purity (..)
    , termEvaluationOrder
    ) where

import PlutusCore.Builtin
import PlutusCore.Pretty
import PlutusIR
import PlutusIR.Contexts

import Control.Lens hiding (Strict)
import Data.DList qualified as DList
import Data.List.NonEmpty qualified as NE
import PlutusCore.Name qualified as PLC
import PlutusIR.Analysis.Builtins
import PlutusIR.Analysis.VarInfo
import Prettyprinter

saturatesScheme :: AppContext tyname name uni fun a -> TypeScheme val args res -> Maybe Bool
-- We've passed enough arguments that the builtin will reduce.
-- Note that this also accepts over-applied builtins.
saturatesScheme _ TypeSchemeResult{}                            = Just True
-- Consume one argument
saturatesScheme (TermAppContext _ _ args) (TypeSchemeArrow sch) = saturatesScheme args sch
saturatesScheme (TypeAppContext _ _ args) (TypeSchemeAll _ sch) = saturatesScheme args sch
-- Under-applied, not saturated
saturatesScheme AppContextEnd TypeSchemeArrow{}                 = Just False
saturatesScheme AppContextEnd TypeSchemeAll{}                   = Just False
-- These cases are only possible in case we have an ill-typed builtin application,
-- so we can't give an answer.
saturatesScheme TypeAppContext{} TypeSchemeArrow{}              = Nothing
saturatesScheme TermAppContext{} TypeSchemeAll{}                = Nothing

-- | Is the given application saturated?
-- Returns 'Nothing' if we can't tell.
isSaturated
    :: forall tyname name uni fun a
    . ToBuiltinMeaning uni fun
    => BuiltinsInfo uni fun
    -> fun
    -> AppContext tyname name uni fun a
    -> Maybe Bool
isSaturated binfo fun args =
  let semvar = binfo ^. biSemanticsVariant
  in case toBuiltinMeaning @uni @fun @(Term TyName Name uni fun ()) semvar fun of
        BuiltinMeaning sch _ _ -> saturatesScheme args sch

-- | Is this pure? Either yes, or maybe not.
data Purity = MaybeImpure | Pure

instance Pretty Purity where
  pretty MaybeImpure = "impure?"
  pretty Pure        = "pure"

-- | Is this term essentially work-free? Either yes, or maybe not.
data WorkFreedom = MaybeWork | WorkFree

instance Pretty WorkFreedom where
  pretty MaybeWork = "maybe work?"
  pretty WorkFree  = "work-free"

-- | Either the "next" term to be evaluated, along with its 'Purity' and 'WorkFreedom',
-- or we don't know what comes next.
data EvalTerm tyname name uni fun a =
  Unknown
  | EvalTerm Purity WorkFreedom (Term tyname name uni fun a)

instance PrettyBy config (Term tyname name uni fun a)
  => PrettyBy config (EvalTerm tyname name uni fun a) where
  prettyBy _ Unknown                    = "<unknown>"
  prettyBy config (EvalTerm eff work t) = pretty eff <+> pretty work <> ":" <+> prettyBy config t

-- We use a DList here for efficient and lazy concatenation
-- | The order in which terms get evaluated, along with their purities.
newtype EvalOrder tyname name uni fun a = EvalOrder (DList.DList (EvalTerm tyname name uni fun a))
  deriving newtype (Semigroup, Monoid)

-- | Get the evaluation order as a list of 'EvalTerm's. Either terminates in a single
-- 'Unknown', which means that we got to a point where evaluation continues but we don't
-- know where; or terminates normally, in which case we actually got to the end of the
-- evaluation order for the term.
unEvalOrder :: EvalOrder tyname name uni fun a -> [EvalTerm tyname name uni fun a]
unEvalOrder (EvalOrder ts) =
  -- This is where we avoid traversing the whole program beyond the first Unknown,
  -- since DList is lazy and we convert to a lazy list and then filter it.
  takeWhileInclusive (\case { Unknown -> False; _ -> True })
  $ DList.toList ts
  where
    takeWhileInclusive :: (a -> Bool) -> [a] -> [a]
    takeWhileInclusive p = foldr (\x ys -> if p x then x:ys else [x]) []

evalThis :: EvalTerm tyname name uni fun a -> EvalOrder tyname name uni fun a
evalThis tm = EvalOrder (DList.singleton tm)

instance PrettyBy config (Term tyname name uni fun a)
  => PrettyBy config (EvalOrder tyname name uni fun a) where
  prettyBy config eo = vsep $ fmap (prettyBy config) (unEvalOrder eo)

{- | Given a term, return the order in which it and its sub-terms will be evaluated.

This aims to be a sound under-approximation: if we don't know, we just say 'Unknown'.
Typically there will be a sequence of terms that we do know, which will terminate
in 'Unknown' once we do something like call a function.

This makes some assumptions about the evaluator, in particular about the order in
which we evaluate sub-terms, but these match the current evaluator and we are not
planning on changing it.
-}
termEvaluationOrder
  :: forall tyname name uni fun a
  . (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique)
  => BuiltinsInfo uni fun
  -> VarsInfo tyname name
  -> Term tyname name uni fun a
  -> EvalOrder tyname name uni fun a
termEvaluationOrder binfo vinfo = goTerm
    where
      goTerm :: Term tyname name uni fun a -> EvalOrder tyname name uni fun a
      goTerm = \case
        t@(Let _ NonRec bs b) ->
          -- first the bindings, in order
          goBindings (NE.toList bs)
          -- then the body
          <> goTerm b
          -- then the whole term, which will lead to applications (so work)
          <> evalThis (EvalTerm Pure MaybeWork t)
        (Let _ Rec _ _)   ->
          -- Hard to know what gets evaluated first in a recursive let-binding,
          -- just give up
          evalThis Unknown

        -- If we can view as a builtin application, then handle that specially
        (splitApplication -> (Builtin a fun, args)) -> goBuiltinApp a fun args
        -- If we can view as a constructor application, then handle that specially.
        -- Constructor applications are always pure: if under-applied they don't
        -- reduce; if fully-applied they are pure; if over-applied it's going to be
        -- a type error since they never return a function. So we can ignore the arity
        -- in this case!
        t@(splitApplication -> (h@(Var _ n), args))
          | Just (DatatypeConstructor{}) <- lookupVarInfo n vinfo ->
            evalThis (EvalTerm Pure MaybeWork h)
            <>
            goAppCtx args
            <>
            evalThis (EvalTerm Pure MaybeWork t)
            -- No Unknown: we go to a known pure place, but we can't show it,
            -- so we just skip it here. This has the effect of making constructor
            -- applications pure

        -- We could handle functions and type abstractions with *known* bodies
        -- here. But there's not much point: beta reduction will immediately
        -- turn those into let-bindings, which we do see through already.
        t@(Apply _ fun arg)    ->
          -- first the function
          goTerm fun
          -- then the arg
          <> goTerm arg
          -- then the whole term, which means environment manipulation, so work
          <> evalThis (EvalTerm Pure MaybeWork t)
          -- then we go to the unknown function body
          <> evalThis Unknown
        t@(TyInst _ ta _)        ->
          -- first the type abstraction
          goTerm ta
          -- then the whole term, which will mean forcing, so work
          <> evalThis (EvalTerm Pure MaybeWork t)
          -- then we go to the unknown body of the type abstraction
          <> evalThis Unknown

        t@(IWrap _ _ _ b)       ->
          -- first the body
          goTerm b
          <> evalThis (EvalTerm Pure WorkFree t)
        t@(Unwrap _ b)          ->
          -- first the body
          goTerm b
          -- then the whole term, but this is erased so it is work-free
          <> evalThis (EvalTerm Pure WorkFree t)
        t@(Constr _ _ _ ts)     ->
          -- first the arguments, in left-to-right order
          foldMap goTerm ts
          -- then the whole term, which means constructing the value, so work
          <> evalThis (EvalTerm Pure MaybeWork t)
        t@(Case _ _ scrut _)    ->
          -- first the scrutinee
          goTerm scrut
          -- then the whole term, which means finding the case so work
          <> evalThis (EvalTerm Pure MaybeWork t)
          -- then we go to an unknown scrutinee
          <> evalThis Unknown

        -- Leaf terms
        t@(Var _ name)      ->
          -- See Note [Purity, strictness, and variables]
          let purity = case varInfoStrictness <$> lookupVarInfo name vinfo of
                Just Strict    -> Pure
                Just NonStrict -> MaybeImpure
                _              -> MaybeImpure
          -- looking up the variable is work
          in evalThis (EvalTerm purity MaybeWork t)
        t@Error{}           ->
          -- definitely effectful! but not relevant from a work perspective
          evalThis (EvalTerm MaybeImpure WorkFree t)
          -- program terminates
          <> evalThis Unknown
        t@Builtin{}         ->
          evalThis (EvalTerm Pure WorkFree t)
        t@TyAbs{}           ->
          evalThis (EvalTerm Pure WorkFree t)
        t@LamAbs{}          ->
          evalThis (EvalTerm Pure WorkFree t)
        t@Constant{}        ->
          evalThis (EvalTerm Pure WorkFree t)

      goBindings ::
        [Binding tyname name uni fun a] ->
        EvalOrder tyname name uni fun a
      goBindings [] = mempty
      goBindings (b:bs) = case b of
        -- Only strict term bindings get evaluated at this point
        TermBind _ Strict _ rhs -> goTerm rhs
        _                       -> goBindings bs

      goBuiltinApp
        :: a
        -> fun
        -> AppContext tyname name uni fun a
        -> EvalOrder tyname name uni fun a
      goBuiltinApp a hd args =
        let
          saturated = isSaturated binfo hd args
          reconstructed = fillAppContext (Builtin a hd) args
          evalEffect = case saturated of
            -- If it's saturated, we might have an effect here
            Just True  -> evalThis (EvalTerm MaybeImpure MaybeWork reconstructed)
            -- TODO: previous definition of work-free included this, it's slightly
            -- unclear if we should do since we do update partial builtin meanings
            -- etc.
            -- If it's unsaturated, we definitely don't, and don't do any work
            Just False -> evalThis (EvalTerm Pure WorkFree reconstructed)
            -- Don't know, be conservative
            Nothing    -> evalThis (EvalTerm MaybeImpure MaybeWork reconstructed)
        in goAppCtx args <> evalEffect

      goAppCtx :: AppContext tyname name uni fun a -> EvalOrder tyname name uni fun a
      goAppCtx = \case
        AppContextEnd           -> mempty
        TermAppContext t _ rest -> goTerm t <> goAppCtx rest
        TypeAppContext _ _ rest -> goAppCtx rest

-- | Will evaluating this term have side effects (looping or error)?
-- This is slightly wider than the definition of a value, as
-- it includes applications that are known to be pure, as well as
-- things that can't be returned from the machine (as they'd be ill-scoped).
isPure ::
    (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique) =>
    BuiltinsInfo uni fun ->
    VarsInfo tyname name ->
    Term tyname name uni fun a ->
    Bool
isPure binfo vinfo t =
  -- to work out if the term is pure, we see if we can look through
  -- the whole evaluation order without hitting something that might be
  -- effectful
  go $ unEvalOrder (termEvaluationOrder binfo vinfo t)
  where
    go :: [EvalTerm tyname name uni fun a] -> Bool
    go [] = True
    go (et:rest) = case et of
      -- Might be an effect here!
      EvalTerm MaybeImpure _ _ -> False
      -- This term is fine, what about the rest?
      EvalTerm Pure _ _        -> go rest
      -- We don't know what will happen, so be conservative
      Unknown                  -> False

{-| Is the given term 'work-free'?

Note: The definition of 'work-free' is a little unclear, but the idea is that
evaluating this term should do very a trivial amount of work.
-}
isWorkFree ::
    (ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique) =>
    BuiltinsInfo uni fun ->
    VarsInfo tyname name ->
    Term tyname name uni fun a ->
    Bool
isWorkFree binfo vinfo t =
  -- to work out if the term is pure, we see if we can look through
  -- the whole evaluation order without hitting something that might be
  -- effectful
  go $ unEvalOrder (termEvaluationOrder binfo vinfo t)
  where
    go :: [EvalTerm tyname name uni fun a] -> Bool
    go [] = True
    go (et:rest) = case et of
      -- Might be an effect here!
      EvalTerm _ MaybeWork _ -> False
      -- This term is fine, what about the rest?
      EvalTerm _ WorkFree _  -> go rest
      -- We don't know what will happen, so be conservative
      Unknown                -> False

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
