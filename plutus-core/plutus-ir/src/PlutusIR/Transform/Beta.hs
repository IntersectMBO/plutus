{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

{-|
A simple beta-reduction pass. -}
module PlutusIR.Transform.Beta
  ( beta
  , betaPass
  , betaPassSC
  ) where

import Control.Lens (over)
import Data.List.NonEmpty qualified as NE
import PlutusCore qualified as PLC
import PlutusIR
import PlutusIR.Pass
import PlutusIR.TypeCheck qualified as TC

{- Note [Multi-beta]
Consider two examples where applying beta should be helpful.

1: [(\x . [(\y . t) b]) a]
2: [[(\x . (\y . t)) a] b]

(1) is the typical "let-binding" pattern: each binding corresponds to an immediately-applied lambda.
(2) is the typical "function application" pattern: a multi-argument function applied to multiple
arguments.

In both cases we would like to produce something like

let
  x = a
  y = b
in t

However, if we naively do a bottom-up pattern-matching transformation on the AST
to look for immediately-applied lambda abstractions then we will get the following:

1:
  [(\x . [(\y . t) b]) a]
  -->
  [(\x . let y = b in t) a]
  ->
  let x = a in let y = b in t

2:
  [[(\x . (\y . t)) a] b]
  -->
  [(let x = a in (\y . t)) b]

Now, if we later lift the let out, then we will be able to see that we can transform (2) further.
But that means that
a) we'd have to do the expensive let-floating pass in every iteration of the
simplifier, and
b) we can only inline one function argument per iteration of the  simplifier, so for a function of
arity N we *must* do at least N passes.

This isn't great, so the solution is to recognize case (2) properly and handle all the arguments in
one go. That will also match cases like (1) just fine, since it's just made up of unary function
applications.

That does mean that we need to do a manual traversal rather than doing standard bottom-up
processing.

Note that multi-beta requires globally unique names. In the example above, we end up with
the binding for `x` outside `b`, which means it could shadow an existing `x` binding in the
environment.

Note that multi-beta cannot be used on TypeBinds. For instance, it is unsound to turn

(/\a \(b : a). t) {x} (y : x)

into

let a = x in let b = y in t

because in order to check that `b` and `y` have the same type, we need to know that `a = x`,
but we don't - type-lets are opaque inside their bodies.
-}

{-| Extract the list of bindings from a term, a bit like a "multi-beta" reduction.

Some examples will help:

[(\x . t) a] -> Just ([x |-> a], t)

[[[(\x . (\y . (\z . t))) a] b] c] -> Just ([x |-> a, y |-> b, z |-> c]) t)

[[(\x . t) a] b] -> Nothing -}
extractBindings
  :: Term tyname name uni fun a
  -> Maybe (NE.NonEmpty (Binding tyname name uni fun a), Term tyname name uni fun a)
extractBindings = collectArgs []
  where
    collectArgs argStack (Apply _ f arg) = collectArgs (arg : argStack) f
    collectArgs argStack t = matchArgs argStack [] t
    matchArgs (arg : rest) acc (LamAbs a n ty body) =
      matchArgs rest (TermBind a Strict (VarDecl a n ty) arg : acc) body
    matchArgs [] acc t =
      case NE.nonEmpty (reverse acc) of
        Nothing -> Nothing
        Just acc' -> Just (acc', t)
    matchArgs (_ : _) _ _ = Nothing

{-|
Recursively apply the beta transformation on the code, both for the terms

@
    (\ (x : A). M) N
    ==>
    let x : A = N in M
@

and types

@
    (/\ a. \(x : a) . x) {A}
    ==>
    let a : * = A in
    (\ (x : A). x)
@ -}
beta
  :: Term tyname name uni fun a
  -> Term tyname name uni fun a
beta = over termSubterms beta . localTransform
  where
    localTransform = \case
      -- See Note [Multi-beta]
      -- This maybe isn't the best annotation for this term, but it will do.
      (extractBindings -> Just (bs, t)) -> Let (termAnn t) NonRec bs t
      -- See Note [Multi-beta] for why we don't perform multi-beta on `TyInst`.
      TyInst _ (TyAbs a n k body) tyArg ->
        let b = TypeBind a (TyVarDecl a n k) tyArg
         in Let (termAnn body) NonRec (pure b) body
      t -> t

betaPassSC
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, PLC.MonadQuote m, Ord a)
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
betaPassSC tcconfig = renamePass <> betaPass tcconfig

betaPass
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, Applicative m, Ord a)
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
betaPass tcconfig =
  NamedPass "beta" $
    Pass
      (pure . beta)
      [Typechecks tcconfig, GloballyUniqueNames]
      [ConstCondition (Typechecks tcconfig)]
