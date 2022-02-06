{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE ViewPatterns #-}
{-|
A simple beta-reduction pass.
-}
module PlutusIR.Transform.Beta (
  beta
  ) where

import PlutusIR
import PlutusIR.Core.Type

import Control.Lens.Setter ((%~))
import Data.Function ((&))
import Data.List.NonEmpty qualified as NE

{- Note [Beta for types]
We can do beta on type abstractions too, turning them into type-lets. We don't do that because
a) It can lead to us inlining types too much, which can slow down compilation a lot.
b) It's currently unsound: https://input-output.atlassian.net/browse/SCP-2570.

We should fix both of these in due course, though.
-}

{- Note [Multi-beta]
Consider two examples where applying beta should be helpful.

1: [(\x . [(\y . t) b]) a]
2: [[(\x . (\y . t)) a] b]

(1) is the typical "let-binding" pattern: each binding corresponds to an immediately-applied lambda.
(2) is the typical "function application" pattern: a multi-argument function applied to multiple arguments.

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
But that means that a) we'd have to do the expensive let-floating pass in every iteration of the simplifier, and
b) we can only inline one function argument per iteration of the  simplifier, so for a function of
arity N we *must* do at least N passes.

This isn't great, so the solution is to recognize case (2) properly and handle all the arguments in one go.
That will also match cases like (1) just fine, since it's just made up of unary function applications.

That does mean that we need to do a manual traversal rather than doing standard bottom-up processing.
-}

{-| Extract the list of bindings from a term, a bit like a "multi-beta" reduction.

Some examples will help:

[(\x . t) a] -> Just ([x |-> a], t)

[[[(\x . (\y . (\z . t))) a] b] c] -> Just ([x |-> a, y |-> b, z |-> c]) t)

[[(\x . t) a] b] -> Nothing

When we decide that we want to do beta for types, we will need to extend this to handle type instantiations too.
-}
extractBindings :: Term tyname name uni fun a -> Maybe (NE.NonEmpty (Binding tyname name uni fun a), Term tyname name uni fun a)
extractBindings = collectArgs []
  where
      collectArgs argStack (Apply _ f arg) = collectArgs (arg:argStack) f
      collectArgs argStack t               = matchArgs argStack [] t
      matchArgs (arg:rest) acc (LamAbs a n ty body) = matchArgs rest (TermBind a Strict (VarDecl a n ty) arg:acc) body
      matchArgs []         acc t                    =
          case NE.nonEmpty (reverse acc) of
              Nothing   -> Nothing
              Just acc' -> Just (acc', t)
      matchArgs (_:_)      _   _                    = Nothing

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
@

-}
beta
    :: Term tyname name uni fun a
    -> Term tyname name uni fun a
beta = \case
    -- See Note [Multi-beta]
    -- This maybe isn't the best annotation for this term, but it will do.
    (extractBindings -> Just (bs, t)) -> Let (termAnn t) NonRec bs (beta t)
    t                                 -> t & termSubterms %~ beta
