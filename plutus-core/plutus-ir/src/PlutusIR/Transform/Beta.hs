{-# LANGUAGE LambdaCase #-}
{-|
A simple beta-reduction pass.

-}
module PlutusIR.Transform.Beta (
  beta
  ) where

import           PlutusPrelude

import           PlutusIR

import           Control.Lens  (transformOf)

{-|
A single non-recursive application of the beta rule.

-}
betaStep
    :: Term tyname name uni fun a
    -> Term tyname name uni fun a
betaStep = \case
    Apply a (LamAbs _ name typ body) arg ->
        let varDecl  = VarDecl a name typ
            binding  = TermBind a Strict varDecl arg
            bindings = binding :| []
        in
            Let a NonRec bindings body
    TyInst a (TyAbs _ tyname kind body) typ ->
        let tyVarDecl = TyVarDecl a tyname kind
            tyBinding = TypeBind a tyVarDecl typ
            bindings  = tyBinding :| []
        in
            Let a NonRec bindings body
    t -> t

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
beta = transformOf termSubterms betaStep
