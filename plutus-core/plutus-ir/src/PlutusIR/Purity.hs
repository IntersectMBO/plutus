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

import Data.Foldable
import Data.List.NonEmpty qualified as NE
import Data.Sequence qualified as Seq
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
    => BuiltinSemanticsVariant fun
    -> fun
    -> AppContext tyname name uni fun a
    -> Maybe Bool
isSaturated semvar fun args =
    case toBuiltinMeaning @uni @fun @(Term TyName Name uni fun ()) semvar fun of
        BuiltinMeaning sch _ _ -> saturatesScheme args sch

-- | Is this pure? Either yes, or maybe not.
data Purity = MaybeImpure | Pure

instance Pretty Purity where
  pretty MaybeImpure = "impure?"
  pretty Pure        = "pure"

-- | Either the "next" term to be evaluated, along with its 'Purity',
-- or we don't know what comes next.
data EvalTerm tyname name uni fun a =
  Unknown
  | EvalTerm Purity (Term tyname name uni fun a)

instance PrettyBy config (Term tyname name uni fun a)
  => PrettyBy config (EvalTerm tyname name uni fun a) where
  prettyBy _ Unknown               = "<unknown>"
  prettyBy config (EvalTerm eff t) = pretty eff <> ":" <+> prettyBy config t

-- We use a Seq here because we want
-- 1. Efficient concatenation for the semigroup instance
-- 2. Quick access to the end of the sequence to check for 'Unknown'
-- We could maybe do this even more efficiently, but Seq should get the job done.
-- | The order in which terms get evaluated, along with their purities.
newtype EvalOrder tyname name uni fun a = EvalOrder (Seq.Seq (EvalTerm tyname name uni fun a))

-- | Get the evaluation order as a list of 'EvalTerm's.
unEvalOrder :: EvalOrder tyname name uni fun a -> [EvalTerm tyname name uni fun a]
unEvalOrder (EvalOrder ts) = toList ts

evalThis :: EvalTerm tyname name uni fun a -> EvalOrder tyname name uni fun a
evalThis tm = EvalOrder (Seq.singleton tm)

instance PrettyBy config (Term tyname name uni fun a)
  => PrettyBy config (EvalOrder tyname name uni fun a) where
  prettyBy config eo = vsep $ fmap (prettyBy config) (unEvalOrder eo)

-- This is still super inefficient, lots of list concatenation here
instance Semigroup (EvalOrder tyname name uni fun a) where
  -- If we have discovered that we don't know where we're going, then no point recording after that
  EvalOrder l@(_ Seq.:|> Unknown) <> EvalOrder _ = EvalOrder l
  EvalOrder l <> EvalOrder r                     = EvalOrder (l <> r)

instance Monoid (EvalOrder tyname name uni fun a) where
  mempty = EvalOrder mempty

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
  . ToBuiltinMeaning uni fun
  => BuiltinSemanticsVariant fun
  -> (name -> Strictness)
  -> Term tyname name uni fun a
  -> EvalOrder tyname name uni fun a
termEvaluationOrder semvar varStrictness = goTerm
    where
      goTerm :: Term tyname name uni fun a -> EvalOrder tyname name uni fun a
      goTerm = \case
        t@(Let _ NonRec bs b) ->
          goBindings (NE.toList bs) -- first the bindings, in order
          <> goTerm b -- then the body
          <> evalThis (EvalTerm Pure t) -- then the whole term
        (Let _ Rec _ _)   ->
          -- Hard to know what gets evaluated first in a recursive let-binding,
          -- just give up
          evalThis Unknown

        -- If we can view as a builtin application, then handle that specially
        (splitApplication -> (Builtin a fun, args)) -> goBuiltinApp a fun args
        -- We could handle functions and type abstractions with *known* bodies
        -- here. But there's not much point: beta reduction will immediately
        -- turn those into let-bindings, which we do see through already.
        t@(Apply _ fun arg)    ->
          goTerm fun -- first the function
          <> goTerm arg -- then the arg
          <> evalThis (EvalTerm Pure t) -- then the whole term
          <> evalThis Unknown -- then we go to the unknown function body
        t@(TyInst _ ta _)        ->
          goTerm ta -- first the type abstraction
          <> evalThis (EvalTerm Pure t) -- then the whole term
          <> evalThis Unknown -- then we go to the unknown body of the type abstraction

        t@(IWrap _ _ _ b)       ->
          goTerm b -- first the body
          <> evalThis (EvalTerm Pure t) -- then the whole term
        t@(Unwrap _ b)          ->
          goTerm b -- first the body
          <> evalThis (EvalTerm Pure t) -- then the whole term
        t@(Constr _ _ _ ts)     ->
          foldMap goTerm ts -- first the arguments, in left-to-right order
          <> evalThis (EvalTerm Pure t) -- then the whole term
        t@(Case _ _ scrut _)    ->
          goTerm scrut -- first the scrutinee
          <> evalThis (EvalTerm Pure t) -- then the whole term
          <> evalThis Unknown -- then we go to an unknown scrutinee

        -- Leaf terms
        t@(Var _ name)      ->
          -- See Note [Purity, strictness, and variables]
          let purity = case varStrictness name of { Strict -> Pure; NonStrict -> MaybeImpure}
          in evalThis (EvalTerm purity t)
        t@Error{}           ->
          evalThis (EvalTerm MaybeImpure t) -- definitely effectful!
          <> evalThis Unknown -- program terminates
        t@Builtin{}         ->
          evalThis (EvalTerm Pure t)
        t@TyAbs{}           ->
          evalThis (EvalTerm Pure t)
        t@LamAbs{}          ->
          evalThis (EvalTerm Pure t)
        t@Constant{}        ->
          evalThis (EvalTerm Pure t)

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
          saturated = isSaturated semvar hd args
          reconstructed = fillAppContext (Builtin a hd) args
          evalEffect = case saturated of
            -- If it's saturated, we might have an effect here
            Just True  -> evalThis (EvalTerm MaybeImpure reconstructed)
            -- If it's unsaturated, we definitely don't
            Just False -> evalThis (EvalTerm Pure reconstructed)
            -- Don't know, be conservative
            Nothing    -> evalThis (EvalTerm MaybeImpure reconstructed)
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
    ToBuiltinMeaning uni fun =>
    BuiltinSemanticsVariant fun ->
    (name -> Strictness) ->
    Term tyname name uni fun a ->
    Bool
isPure semvar varStrictness t =
  -- to work out if the term is pure, we see if we can look through
  -- the whole evaluation order without hitting something that might be
  -- effectful
  go $ unEvalOrder (termEvaluationOrder semvar varStrictness t)
  where
    go :: [EvalTerm tyname name uni fun a] -> Bool
    go [] = True
    go (et:rest) = case et of
      -- Might be an effect here!
      EvalTerm MaybeImpure _ -> False
      -- This term is fine, what about the rest?
      EvalTerm Pure _        -> go rest
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
