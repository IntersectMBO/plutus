{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
-- | Functions for computing variable usage inside terms and types.
module Language.PlutusIR.Analysis.Usages (runTermUsages, runTypeUsages, Usages, isUsed, allUsed) where

import           Language.PlutusIR

import qualified Language.PlutusCore      as PLC
import qualified Language.PlutusCore.Name as PLC

import           Control.Lens
import           Control.Monad.State

import           Data.Coerce
import           Data.Foldable
import qualified Data.Map                 as Map
import qualified Data.Set                 as Set

-- | Variable uses, as a map from the 'PLC.Unique' to its usage count. Unused variables may be missing
-- or have usage count 0.
type Usages = Map.Map PLC.Unique Int

addUsage :: (PLC.HasUnique n unique) => n -> Usages -> Usages
addUsage n usages =
    let
        u = coerce $ n ^. PLC.unique
        old = Map.findWithDefault 0 u usages
    in Map.insert u (old+1) usages

isUsed :: (PLC.HasUnique n unique) => n -> Usages -> Bool
isUsed n usages = Map.findWithDefault 0 (n ^. PLC.unique . coerced) usages > 0

allUsed :: Usages -> Set.Set PLC.Unique
allUsed usages = Map.keysSet $ Map.filter (> 0) usages

-- | Compute the 'Usages' for a 'Term'.
runTermUsages
    :: (PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Term tyname name a
    -> Usages
runTermUsages term = execState (termUsages term) mempty

-- | Compute the 'Usages' for a 'Type'.
runTypeUsages
    ::(PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Type tyname a
    -> Usages
runTypeUsages ty = execState (typeUsages ty) mempty

termUsages
    :: (MonadState Usages m, PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Term tyname name a
    -> m ()
termUsages term = case term of
    Let _ _ bs t      -> traverse_ bindingUsages bs >> termUsages t
    Var _ n           -> modify (addUsage n)
    TyAbs _ _ _ t     -> termUsages t
    LamAbs _ _ ty t   -> typeUsages ty >> termUsages t
    Apply _ t1 t2     -> termUsages t1 >> termUsages t2
    TyInst _ t ty     -> termUsages t >> typeUsages ty
    Error _ ty        -> typeUsages ty
    IWrap _ pat arg t -> typeUsages pat >> typeUsages arg >> termUsages t
    Unwrap _ t        -> termUsages t
    Constant _ _      -> pure ()
    Builtin _ _       -> pure ()

varDeclUsages
    :: (MonadState Usages m, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => VarDecl tyname name a
    -> m ()
varDeclUsages (VarDecl _ _ ty) = typeUsages ty

-- Here for completeness but doesn't do much. Would matter if we had kind variables we had to check for.
tyVarDeclUsages
    :: (MonadState Usages m)
    => TyVarDecl tyname a
    -> m ()
tyVarDeclUsages _ = pure ()

bindingUsages
    :: (MonadState Usages m, PLC.HasUnique (name a) PLC.TermUnique, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Binding tyname name a
    -> m ()
bindingUsages = \case
    TermBind _ _ rhs -> termUsages rhs
    TypeBind _ _ rhs -> typeUsages rhs
    DatatypeBind _ (Datatype _ d tvs _ constrs) -> do
        tyVarDeclUsages d
        traverse_ tyVarDeclUsages tvs
        traverse_ varDeclUsages constrs

-- TODO: move to language-plutus-core
typeUsages
    :: (MonadState Usages m, PLC.HasUnique (tyname a) PLC.TypeUnique)
    => Type tyname a
    -> m ()
typeUsages ty = case ty of
    TyVar _ n        -> modify (addUsage n)
    TyFun _ t1 t2    -> typeUsages t1 >> typeUsages t2
    TyIFix _ pat arg -> typeUsages pat >> typeUsages arg
    TyForall _ _ _ t -> typeUsages t
    TyLam _ _ _ t    -> typeUsages t
    TyApp _ t1 t2    -> typeUsages t1 >> typeUsages t2
    TyBuiltin _ _    -> pure ()
