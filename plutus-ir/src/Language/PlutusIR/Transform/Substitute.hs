{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
-- | Implements naive substitution functions for replacing type and term variables.
module Language.PlutusIR.Transform.Substitute (substTerm, PLC.substTy, substBinding) where

import           Language.PlutusIR

import qualified Language.PlutusCore.Subst as PLC

-- | Naively substitute names using the given functions (i.e. do not account for scoping).
substTerm ::
  (tyname a -> Maybe (Type tyname a)) ->
  (name a -> Maybe (Term tyname name a)) ->
  Term tyname name a ->
  Term tyname name a
substTerm tynameF nameF = \case
    Var a bnd          -> case nameF bnd of
      Just t  -> t
      Nothing -> Var a bnd
    LamAbs a bnd ty t  -> LamAbs a bnd (sTy ty) (sTerm t)
    TyInst a t ty      -> TyInst a (sTerm t) (sTy ty)
    IWrap a pat arg t  -> IWrap a (sTy pat) (sTy arg) (sTerm t)
    Error a ty         -> Error a (sTy ty)
    Let a r bs t       -> Let a r (fmap (substBinding tynameF nameF) bs) (sTerm t)
    TyAbs a tn k t     -> TyAbs a tn k (sTerm t)
    Apply a t1 t2      -> Apply a (sTerm t1) (sTerm t2)
    Unwrap a t         -> Unwrap a (sTerm t)
    x                  -> x
    where
        sTerm = substTerm tynameF nameF
        sTy = PLC.substTy tynameF

substVarDecl ::
  (tyname a -> Maybe (Type tyname a)) ->
  (name a -> Maybe (Term tyname name a)) ->
  VarDecl tyname name a ->
  VarDecl tyname name a
substVarDecl tynameF _ (VarDecl x n ty) = VarDecl x n (PLC.substTy tynameF ty)

substTyVarDecl ::
  (tyname a -> Maybe (Type tyname a)) ->
  TyVarDecl tyname a ->
  TyVarDecl tyname a
substTyVarDecl _ (TyVarDecl x tn k) = TyVarDecl x tn k

-- | Naively substitute names using the given functions (i.e. do not account for scoping).
substBinding ::
  (tyname a -> Maybe (Type tyname a)) ->
  (name a -> Maybe (Term tyname name a)) ->
  Binding tyname name a ->
  Binding tyname name a
substBinding tynameF nameF = \case
    TermBind x vd t -> TermBind x (sVd vd) (sTerm t)
    TypeBind x tvd ty -> TypeBind x (sTyVd tvd) (sTy ty)
    DatatypeBind x (Datatype x' tvd tvs destr constrs) ->
        DatatypeBind x (Datatype x' (sTyVd tvd) (fmap sTyVd tvs) destr (fmap sVd constrs))
    where
        sTerm = substTerm tynameF nameF
        sTy = PLC.substTy tynameF
        sVd = substVarDecl tynameF nameF
        sTyVd = substTyVarDecl tynameF
