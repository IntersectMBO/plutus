{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Functions for computing the free (type-)variables of a PIR term or type.
module Language.PlutusIR.Analysis.Free (fTerm, fType) where

import           Language.PlutusIR

import qualified Language.PlutusCore       as PLC
import qualified Language.PlutusCore.Name  as PLC

import           Language.PlutusCore.Subst (ftvTy)

import           Control.Lens

import qualified Data.Set                  as S

{- Note: [PIR Free variables]

The functions of this module behave similar to those found in 'language-plutus-core/src/Language/PlutusCore/Subst.hs',
with the difference:

- extended to support the plutus-ir (letrec and letnonrec)
- place the free variables and free type variables in the same set of uniques.

The functions do not require that the input term be prior 'renamed'/'uniqueified'.
-}


{- Note [Free variables and letnonrec linear scope]

Let (nonrec) is linearly scoped, as shown by the example:

let b1 = rhs1;
    b2 = rhs2  (b1 is visible in rhs2);
in ...

is the same as as let b1 = rhs in (let b2 = rhs2 in ... )

And is different than letrec where all identifiers are visible/scoped:

let b1 = rhs1 (b2 is visible in rhs1);
    b2 = rhs2  (b1 is visible in rhs2);
in ...


In this regard, extra care has been taken when counting the free variables of a letnorec vs a letrec, as
shown by the example:

(let nonrec { x = y
              y = 3 }
) ===> y is free in x

VS

(let rec { x = y
           y = 3 }
) ===> y is not free in x

-}


-- | Given a term, it returns a set of all the FREE variables inside that term (i.e. not declared/scoped inside the term).
--
-- It does not require the input term to be prior 'PLC.rename'd.
-- TODO: refactor using recursion-schemes (or usingtermSubterms, termSubtypes can be used and lens + fold), see 'language-plutus-core/src/Language/PlutusCore/Subst.hs'
-- See Note: [PIR Free variables]
fTerm :: forall name tyname a.
  (Ord (tyname a), PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
  => Term tyname name a -> S.Set PLC.Unique
fTerm = \case
  Var _ x -> S.singleton $ x ^. PLC.unique . coerced

  Let _ NonRec bs tIn -> fLet bs tIn NonRec
  Let _ Rec bs tIn -> fLet bs tIn Rec

  TyAbs _ n _ t -> S.delete (n ^. PLC.unique . coerced) $ fTerm t
  LamAbs _ n ty t -> fType ty
                     <>
                     S.delete (n ^. PLC.unique . coerced) (fTerm t)
  Apply _ t1 t2 -> fTerm t1 <> fTerm t2
  TyInst _ t ty -> fTerm t <> fType ty
  IWrap _ ty1 ty2 t -> mconcat [fType ty1, fType ty2, fTerm t]
  Unwrap _ t -> fTerm t
  _ -> S.empty

 where
  fLet :: [Binding tyname name a] -> Term tyname name a -> Recursivity -> S.Set PLC.Unique
  fLet bs tIn =
    let fIn = fTerm tIn S.\\ foldMap bindingIds bs -- the free variables of termIn (scoped by all the let id's)
    in \case
      Rec -> (foldMap fBinding bs S.\\ foldMap bindingIds bs) <> fIn -- all id's in the letrec can be seen (scoped) by each other
      NonRec -> let initialScope = S.empty -- starting with an empty linear-scope
                    initialFreeSet = fIn -- starting from the freeset found in tIn
                in snd $ foldl nonRecVarAcc (initialScope, initialFreeSet) bs

  -- it threads an ever-increasing linear-scope and an accumulated set of free variables found, i.e. (linearScope, freeSet)
  -- See Note [Free variables and letnonrec linear scope]
  -- See Note [Right-associative compilation of let-bindings for linear scoping]
  nonRecVarAcc :: (S.Set PLC.Unique, S.Set PLC.Unique) -> Binding tyname name a -> (S.Set PLC.Unique, S.Set PLC.Unique)
  nonRecVarAcc (accLinearScope,accFreeSet) b =
    let newScope = bindingIds b <> accLinearScope
        newFreeSet = (fBinding b S.\\ accLinearScope) <> accFreeSet
    in (newScope, newFreeSet)

  fBinding ::  Binding tyname name a -> S.Set PLC.Unique
  fBinding = \case
    TermBind _ _ (VarDecl _ _ ty) tRhs -> fType ty <> fTerm tRhs
    DatatypeBind _ (Datatype _ _ _ _ constrs) -> foldMap fVarDecl constrs
    TypeBind _ (TyVarDecl _ _ _k) tyRhs -> fType tyRhs

  fVarDecl :: VarDecl tyname name a -> S.Set PLC.Unique
  fVarDecl (VarDecl _ _ ty) = fType ty

  bindingIds :: Binding tyname name a -> S.Set PLC.Unique
  bindingIds = \case
    TermBind _ _ (VarDecl _ n _) _ -> S.singleton (n^.PLC.unique.coerced)
    DatatypeBind _ dt -> datatypeIds dt
    TypeBind _ (TyVarDecl _ n _) _ -> S.singleton (n^.PLC.unique.coerced)

-- | Given a PIR type, it returns the free type variables of that type.
-- See Note: [PIR Free variables]
fType :: (Ord (tyname a), PLC.HasUnique (tyname a) PLC.TypeUnique)
  => Type tyname a -> S.Set PLC.Unique
fType = S.map (^. PLC.unique . coerced) . ftvTy
