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
import Control.Monad.Extra
import Control.Monad.Trans.Reader
import Data.Foldable (foldrM)
import Data.List.Extra qualified as List
import Data.List.NonEmpty.Extra (NonEmpty (..))
import Data.List.NonEmpty.Extra qualified as NonEmpty
import Data.Set (Set)
import Data.Set qualified as Set
import PlutusIR.Analysis.Builtins
import PlutusIR.Analysis.VarInfo

{- Note [Float-in]

-------------------------------------------------------------------------------
1. Which term bindings can be floated in?
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
2. What about type and datatype bindings?
-------------------------------------------------------------------------------

Type bindings can always be floated in. Doing so has no impact on cost since the a type
binding is compiled into a `force`/`delay` pair that will be optimized away. However,
doing so may enable other type and datatype bindings to be floated inwards.

Datatype bindings can also always be floated inwards. A `DatatypeBind` defines both new types
and new terms. The types can always be floated in, and the terms are all lambda abstractions
or type abstractions, which are essentially work free.

-------------------------------------------------------------------------------
3. The effect of floating in
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
4. When can floating-in increase costs?
-------------------------------------------------------------------------------

Floating-in a binding can increase cost only if the binding is originally outside of `X`,
and is floated into `X`, and `X` satisfies both of the following conditions:

(1) `X` is a lambda abstraction, a type abstraction, or the RHS of a non-strict binding
(recall that the RHS of a non-strict binding is equivalent to a type abstraction).

(2) `X` is in the RHS of a (either strict or non-strict) binding whose LHS is used more than once.

Note the "only if" - the above are the necessary conditions, but not sufficient. Also note
that this is in the context of the float-in pass itself. Floating a binding in /can/ affect
ther subsequent optimizations in a negative way (e.g., inlining).

Therefore, to avoid the possibility of float-in increasing costs, we should avoid
floating-in if the above conditions are met.

-------------------------------------------------------------------------------
5. Implementation of the float-in pass
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
(2) When `ctxtInManyOccRhs = True`, we additionally avoid descending into `LamAbs`, `TyAbs`,
and the RHS of a non-strict binding whose LHS is used only once.

-------------------------------------------------------------------------------
6. Relaxation of the float-in criteria
-------------------------------------------------------------------------------

Experimentation using our test suites indicates that the above criteria is too
conservative (there's no cost saving if we adhere to them). We relax the criteria
by allowing a binding to be floated into lambda abstractions or type abstractions,
even if they are in the RHS of a multi-use binding or the argument of an application.

Why does that make sense? Because, as said before, the savings created by float-in
comes from floating bindings into unused branches. A branch of an `if`-expression
is either a value, or a type abstraction (see Note [Case expressions and laziness]).
If it is a value and contains an unused variable, the unused variable is most likely
(if not always) behind a lambda abstraction or a type abstraction. Therefore, by
always allowing a binding to be floated into lambda/type abstractions, the chance
that it is floated into an unused branch is greatly increased.

The relaxation reduces the costs of several test cases (in one case, "formulaBudget",
the saving is significant), although it does increase the cost of one test case ("knightsBudget").

The relaxation is on by default, and can be turned off with flag `no-relaxed-float-in`
or flag `conservative-optimisation`.

-}

-- | The uniques of all used variables in a term.
type Uniques = Set PLC.Unique

data FloatInContext = FloatInContext
  { _ctxtInManyOccRhs :: Bool
  -- ^ Whether we are in the RHS of a binding whose LHS is used more than once.
  -- See Note [Float-in] #5
  , _ctxtUsages       :: Usages.Usages
  , _ctxtRelaxed      :: Bool
  -- ^ Whether to float-in more aggressively. See Note [Float-in] #6
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
  BuiltinsInfo uni fun ->
  -- | Whether to float-in more aggressively. See Note [Float-in] #6
  Bool ->
  Term tyname name uni fun a ->
  m (Term tyname name uni fun a)
floatTerm binfo relaxed t0 = do
  t1 <- PLC.rename t0
  pure . fmap fst $ floatTermInner (Usages.termUsages t1) (termVarInfo t1) t1
  where
    floatTermInner ::
      Usages.Usages ->
      VarsInfo tyname name ->
      Term tyname name uni fun a ->
      Term tyname name uni fun (a, Uniques)
    floatTermInner usgs vinfo = go
      where
        -- Float bindings in the given `Term` inwards, and annotate each term with the set of
        -- `Unique`s of used variables in the `Term`.
        go ::
          Term tyname name uni fun a ->
          Term tyname name uni fun (a, Uniques)
        go t = case t of
          Apply a fun0 arg0 ->
            let fun = go fun0
                arg = go arg0
                us = termUniqs fun <> termUniqs arg
             in Apply (a, us) fun arg
          LamAbs a n ty0 body0 ->
            let ty = goType ty0
                body = go body0
             in LamAbs (a, typeUniqs ty <> termUniqs body) n ty body
          TyAbs a n k body0 ->
            let body = go body0
             in TyAbs (a, termUniqs body) n (noUniq k) body
          TyInst a body0 ty0 ->
            let body = go body0
                ty = goType ty0
             in TyInst (a, termUniqs body <> typeUniqs ty) body ty
          IWrap a patTy0 argTy0 body0 ->
            let patTy = goType patTy0
                argTy = goType argTy0
                body = go body0
             in IWrap
                  (a, typeUniqs patTy <> typeUniqs argTy <> termUniqs body)
                  patTy
                  argTy
                  body
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
                  (foldrM (floatInBinding binfo vinfo a) body bs)
                  (FloatInContext False usgs relaxed)
          Let a Rec bs0 body0 ->
            -- Currently we don't move recursive bindings, so we simply descend into the body.
            let bs = goBinding <$> bs0
                body = go body0
                us = termUniqs body <> foldMap bindingUniqs bs
             in Let (a, us) Rec bs body
          Var a n -> Var (a, Set.singleton (n ^. PLC.theUnique)) n
          Error a ty0 ->
            let ty = goType ty0
             in Error (a, typeUniqs ty) ty
          Constr a ty0 i es0 ->
            let
              ty = goType ty0
              es = fmap go es0
              us = typeUniqs ty <> foldMap termUniqs es
             in
              Constr (a, us) ty i es
          Case a ty0 arg0 cs0 ->
            let
              ty = goType ty0
              arg = go arg0
              cs = fmap go cs0
              us = typeUniqs ty <> termUniqs arg <> foldMap termUniqs cs
             in
              Case (a, us) ty arg cs
          Constant{} -> noUniq t
          Builtin{} -> noUniq t

        -- Float bindings in the given `Binding` inwards, and calculate the set of
        -- `Unique`s of used variables in the result `Binding`.
        goBinding ::
          Binding tyname name uni fun a ->
          Binding tyname name uni fun (a, Uniques)
        goBinding = \case
          TermBind a s var0 rhs0 ->
            let var = goVarDecl var0
                rhs = go rhs0
             in TermBind (a, termUniqs rhs <> varDeclUniqs var) s var rhs
          TypeBind a tvar rhs0 ->
            let rhs = goType rhs0
             in -- A `TyVarDecl` does not use any variable, hence `noUniq`.
                TypeBind (a, typeUniqs rhs) (noUniq tvar) rhs
          DatatypeBind a (Datatype a' tv tvs destr constrs0) ->
            -- The constructors in a `Datatype` may use type variables.
            let constrs = goVarDecl <$> constrs0
                us = foldMap varDeclUniqs constrs
             in DatatypeBind
                  (a, us)
                  (Datatype (a', us) (noUniq tv) (noUniq <$> tvs) destr constrs)

        -- Calculate the set of `Unique`s of used variables in a `Type`.
        goType :: Type tyname uni a -> Type tyname uni (a, Uniques)
        goType = \case
          TyVar a n -> TyVar (a, Set.singleton (n ^. PLC.theUnique)) n
          TyFun a argTy0 resTy0 ->
            let argTy = goType argTy0
                resTy = goType resTy0
                us = typeUniqs argTy <> typeUniqs resTy
             in TyFun (a, us) argTy resTy
          TyIFix a patTy0 argTy0 ->
            let patTy = goType patTy0
                argTy = goType argTy0
                us = typeUniqs patTy <> typeUniqs argTy
             in TyIFix (a, us) patTy argTy
          TyForall a n k bodyTy0 ->
            let bodyTy = goType bodyTy0
                us = typeUniqs bodyTy
             in TyForall (a, us) n (noUniq k) bodyTy
          TyBuiltin a t -> TyBuiltin (a, mempty) t
          TyLam a n k bodyTy0 ->
            let bodyTy = goType bodyTy0
                us = typeUniqs bodyTy
             in TyLam (a, us) n (noUniq k) bodyTy
          TyApp a funTy0 argTy0 ->
            let funTy = goType funTy0
                argTy = goType argTy0
                us = typeUniqs funTy <> typeUniqs argTy
             in TyApp (a, us) funTy argTy
          TySOP a tyls ->
            let tyls' = (fmap . fmap) goType tyls
                us = (foldMap . foldMap) typeUniqs tyls'
             in TySOP (a, us) tyls'

        -- Calculate the set of `Unique`s of used variables in a `VarDecl`.
        -- The type of the declared variable may use type variables.
        goVarDecl :: VarDecl tyname name uni a -> VarDecl tyname name uni (a, Uniques)
        goVarDecl (VarDecl a n ty0) = VarDecl (a, typeUniqs ty) n ty
          where
            ty = goType ty0

-- | The set of `Unique`s of used variables in a `Term`.
termUniqs :: Term tyname name uni fun (a, Uniques) -> Uniques
termUniqs = snd . termAnn

-- | The set of `Unique`s of used variables in a `Type`.
typeUniqs :: Type tyname uni (a, Uniques) -> Uniques
typeUniqs = snd . PLC.typeAnn

-- | The set of `Unique`s of used variables in the RHS of a `Binding`.
bindingUniqs :: Binding tyname name uni fun (a, Uniques) -> Uniques
bindingUniqs = snd . bindingAnn

-- | The set of `Unique`s of used variables in a `VarDecl`.
varDeclUniqs :: VarDecl tyname name uni (a, Uniques) -> Uniques
varDeclUniqs = snd . view PLC.varDeclAnn

noUniq :: (Functor f) => f a -> f (a, Uniques)
noUniq = fmap (,mempty)

-- See Note [Float-in] #1
floatable
    :: (PLC.ToBuiltinMeaning uni fun, PLC.HasUnique name PLC.TermUnique)
    => BuiltinsInfo uni fun
    -> VarsInfo tyname name
    -> Binding tyname name uni fun a
    -> Bool
floatable binfo vinfo = \case
  -- See Note [Float-in] #1
  TermBind _a Strict _var rhs     -> isWorkFree binfo vinfo rhs
  TermBind _a NonStrict _var _rhs -> True
  -- See Note [Float-in] #2
  TypeBind{}                      -> True
  -- See Note [Float-in] #2
  DatatypeBind{}                  -> True

{- | Given a `Term` and a `Binding`, determine whether the `Binding` can be
 placed somewhere inside the `Term`.

 If yes, return the result `Term`. Otherwise, return a `Let` constructed from
 the given `Binding` and `Term`.
-}
floatInBinding ::
  forall tyname name uni fun a.
  ( PLC.HasUnique name PLC.TermUnique
  , PLC.HasUnique tyname PLC.TypeUnique
  , PLC.ToBuiltinMeaning uni fun
  ) =>
  BuiltinsInfo uni fun ->
  VarsInfo tyname name ->
  -- | Annotation to be attached to the constructed `Let`.
  a ->
  Binding tyname name uni fun (a, Uniques) ->
  Term tyname name uni fun (a, Uniques) ->
  Reader FloatInContext (Term tyname name uni fun (a, Uniques))
floatInBinding binfo vinfo letAnn = \b ->
  if floatable binfo vinfo b
    then go b
    else \body ->
      let us = termUniqs body <> bindingUniqs b
       in pure $ Let (letAnn, us) NonRec (pure b) body
  where
    go ::
      Binding tyname name uni fun (a, Uniques) ->
      Term tyname name uni fun (a, Uniques) ->
      Reader FloatInContext (Term tyname name uni fun (a, Uniques))
    go b !body = case body of
      Apply (a, usBody) fun arg
        | Set.disjoint declaredUniqs (termUniqs fun) -> do
            -- `fun` does not mention the binding, so we can place the binding
            -- inside `arg`.
            -- See Note [Float-in] #4
            usgs <- asks (view ctxtUsages)
            let inManyOccRhs = case fun of
                  LamAbs _ name _ _ ->
                    Usages.getUsageCount name usgs > 1
                  Builtin{} -> False
                  -- We need to be conservative here, this could be something
                  -- that computes to a function that uses its argument repeatedly.
                  _ -> True
            Apply (a, usBind <> usBody) fun
              <$> local (over ctxtInManyOccRhs (|| inManyOccRhs)) (go b arg)
        | Set.disjoint declaredUniqs (termUniqs arg) ->
            -- `arg` does not mention the binding, so we can place the binding
            -- inside `fun`.
            Apply (a, usBind <> usBody) <$> go b fun <*> pure arg
      LamAbs (a, usBody) n ty lamAbsBody
        | Set.disjoint declaredUniqs (typeUniqs ty) ->
            -- See Note [Float-in] #6
            ifM
              (asks (view ctxtInManyOccRhs) &&^ notM (asks (view ctxtRelaxed)))
              giveup
              (LamAbs (a, usBind <> usBody) n ty <$> go b lamAbsBody)
      TyAbs (a, usBody) n k tyAbsBody ->
        -- See Note [Float-in] #6
        ifM
          (asks (view ctxtInManyOccRhs) &&^ notM (asks (view ctxtRelaxed)))
          giveup
          (TyAbs (a, usBind <> usBody) n k <$> go b tyAbsBody)
      TyInst (a, usBody) tyInstBody ty
        | Set.disjoint declaredUniqs (typeUniqs ty) ->
            -- A binding can always be placed inside the body a `TyInst` if `ty`
            -- doesn't use any of the `declaredUniqs`.
            TyInst (a, usBind <> usBody) <$> go b tyInstBody <*> pure ty
      Let (a, usBody) NonRec bs letBody
        -- The binding can be placed inside a `Let`, if the right hand sides of the
        -- bindings of the `Let` do not mention `var`.
        | Set.disjoint declaredUniqs (foldMap bindingUniqs bs) ->
            Let (a, usBind <> usBody) NonRec bs <$> go b letBody
        | Set.disjoint declaredUniqs (termUniqs letBody)
        , Just (before, TermBind (a', usBind') s' var' rhs', after) <-
            findNonDisjoint declaredUniqs (NonEmpty.toList bs) bindingUniqs
        , -- The LHS (declared variable) must not use any uniques in `us`. Only the RHS is
          -- allowed to use them. Otherwise we cannot float a binding whose unique set is `us`
          -- into the RHS of this `TermBind`.
          Set.disjoint declaredUniqs (varDeclUniqs var') ->
            do
              -- `letBody` does not mention `var`, and there is exactly one
              -- RHS in `bs` that mentions `var`, so we can place `b`
              -- inside one of the RHSs in `bs`.
              ctxt <- ask
              let usageCnt = Usages.getUsageCount var' (ctxt ^. ctxtUsages)
                  safe = case s' of
                    Strict -> True
                    NonStrict ->
                      not (ctxt ^. ctxtInManyOccRhs)
                        -- Descending into a non-strict binding whose LHS is used
                        -- more than once should be avoided, regardless of
                        -- `ctxtInManyOccRhs`.
                        -- See Note [Float-in] #4
                        && usageCnt <= 1
                  inManyOccRhs = usageCnt > 1
              if safe
                then do
                  b'' <-
                    TermBind (a', usBind <> usBind') s' var'
                      <$> local
                        (over ctxtInManyOccRhs (|| inManyOccRhs))
                        (go b rhs')
                  let bs' = NonEmpty.appendr before (b'' :| after)
                  pure $ Let (a, usBind <> usBody) NonRec bs' letBody
                else giveup
      IWrap (a, usBody) ty1 ty2 iwrapBody
        | Set.disjoint declaredUniqs (typeUniqs ty1)
        , Set.disjoint declaredUniqs (typeUniqs ty2) ->
            -- A binding can be placed inside an `IWrap`, if `ty1` and `ty2`
            -- do not use any of the `declaredUniqs`.
            IWrap (a, usBind <> usBody) ty1 ty2 <$> go b iwrapBody
      Unwrap (a, usBody) unwrapBody ->
        -- A binding can always be placed inside an `Unwrap`.
        Unwrap (a, usBind <> usBody) <$> go b unwrapBody
      Constr (a, usBody) ty i es
        | Set.disjoint declaredUniqs (typeUniqs ty)
        , Just (before, t, after) <-
            findNonDisjoint declaredUniqs es termUniqs ->
            do
              t' <- go b t
              pure $ Constr (a, usBind <> usBody) ty i (before ++ [t'] ++ after)
      Case (a, usBody) ty arg cs
        | Set.disjoint declaredUniqs (typeUniqs ty)
        , Set.disjoint declaredUniqs (termUniqs arg)
        , Just (before, c, after) <-
            findNonDisjoint declaredUniqs cs termUniqs ->
            do
              c' <- go b c
              pure $ Case (a, usBind <> usBody) ty arg (before ++ [c'] ++ after)
        | Set.disjoint declaredUniqs (typeUniqs ty)
        , all (\c -> Set.disjoint declaredUniqs (termUniqs c)) cs ->
            do
              arg' <- go b arg
              pure $ Case (a, usBind <> usBody) ty arg' cs
      _ -> giveup
      where
        giveup =
          let us = termUniqs body <> bindingUniqs b
           in pure $ Let (letAnn, us) NonRec (pure b) body
        declaredUniqs = Set.fromList $ b ^.. bindingIds
        usBind = bindingUniqs b

{- |
Search the given list of elements for the unique one whose 'Uniques' are non-disjoint
with the given 'Uniques'. Then, split the list at that point.
-}
findNonDisjoint :: Uniques -> [t] -> (t -> Uniques) -> Maybe ([t], t, [t])
findNonDisjoint us bs getUniques = case is of
  [(t, i)] -> Just (take i bs, t, drop (i + 1) bs)
  _        -> Nothing
  where
    is = List.filter (\(t, _) -> not $ getUniques t `Set.disjoint` us) (bs `zip` [0 ..])
