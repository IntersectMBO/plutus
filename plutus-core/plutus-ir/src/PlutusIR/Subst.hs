{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module PlutusIR.Subst
    ( uniquesTerm
    , uniquesType
    , fvTerm
    , ftvTerm
    , fvBinding
    , ftvBinding
    , ftvTy
    ) where

import PlutusCore.Core.Type qualified as PLC
import PlutusCore.Name qualified as PLC
import PlutusCore.Subst (ftvTy, uniquesType)

import PlutusIR.Compiler.Datatype
import PlutusIR.Core

import Control.Lens
import Data.Set as S hiding (foldr)
import Data.Set.Lens (setOf)

uniquesTerm
    :: PLC.HasUniques (Term tyname name uni fun ann)
    => Term tyname name uni fun ann -> Set PLC.Unique
uniquesTerm = setOf termUniquesDeep

-- | Get all the free term variables in a PIR term.
fvTerm :: Ord name => Term tyname name uni fun ann -> Set name
fvTerm = \case
    Let _ NonRec bs tIn ->
        let fvLinearScope b acc = fvBinding b
                                   <> (acc \\ setOf bindingNames b)
        in foldr fvLinearScope (fvTerm tIn) bs

    Let _ Rec bs tIn ->
        (foldMap fvBinding bs <> fvTerm tIn)
        \\ setOf (traversed.bindingNames) bs

    LamAbs _ n _ t -> delete n $ fvTerm t
    Apply _ t1 t2 -> fvTerm t1 <> fvTerm t2
    Var _ n -> singleton n
    TyAbs _ _ _ t ->   fvTerm t
    TyInst _ t _ ->    fvTerm t
    Unwrap _ t ->      fvTerm t
    IWrap _ _ _ t ->   fvTerm t
    Constant{}       -> mempty
    Builtin{}        -> mempty
    Error{}          -> mempty

-- | Get all the free type variables in a PIR term.
ftvTerm :: Ord tyname => Term tyname name uni fun ann -> Set tyname
ftvTerm = \case
    Let _ r@NonRec bs tIn ->
        let ftvLinearScope b acc = ftvBinding r b
                                   <> (acc \\ setOf bindingTyNames b)
        in foldr ftvLinearScope (ftvTerm tIn) bs

    Let _ r@Rec bs tIn ->
        (ftvTerm tIn <> foldMap (ftvBinding r) bs)
        \\ setOf (traversed.bindingTyNames) bs
    TyAbs _ ty _ t    -> delete ty $ ftvTerm t
    LamAbs _ _ ty t   -> ftvTy ty <> ftvTerm t
    Apply _ t1 t2     -> ftvTerm t1 <> ftvTerm t2
    TyInst _ t ty     -> ftvTerm t <> ftvTy ty
    Unwrap _ t        -> ftvTerm t
    IWrap _ pat arg t -> ftvTy pat <> ftvTy arg <> ftvTerm t
    Error _ ty        -> ftvTy ty
    Var{}               -> mempty
    Constant{}          -> mempty
    Builtin{}           -> mempty

-- | Get all the free variables in a PIR single let-binding.
fvBinding :: Ord name => Binding tyname name uni fun ann -> Set name
fvBinding b = mconcat $ fvTerm <$> ( b^..bindingSubterms)

-- | Get all the free type variables in a PIR single let-binding.
ftvBinding :: forall tyname name uni fun ann.
             Ord tyname => Recursivity -> Binding tyname name uni fun ann -> Set tyname
ftvBinding r b = mconcat $ ftvTs ++ ftvTys
 where
    ftvTs = ftvTerm <$> b^..bindingSubterms
    ftvTys = ftvTyDataSpecial <$> b^..bindingSubtypes

    -- like ftvTy but specialized for the datatypebind case
    ftvTyDataSpecial :: Type tyname uni ann -> Set tyname
    ftvTyDataSpecial ty = case b of
        DatatypeBind _ (Datatype _ tyconstr tyvars _ _) -> case r of
            -- for rec, both tyconstr+tyvars are in scope in *WHOLE* dataconstructors
            Rec -> ftvTy ty \\ setOf bindingTyNames b
            NonRec ->
                let tyvarsNames = setOf (traversed.PLC.tyVarDeclName) tyvars
                    ftvDom = mconcat $ ftvTy <$> funTyArgs ty
                    -- tyconstr is in scope *only* in the result type codomain
                    ftvCod = ftvTy (funResultType ty) \\ setOf PLC.tyVarDeclName tyconstr
                -- for nonrec, the tyvars are in scope in *WHOLE* dataconstructors
                in (ftvDom <> ftvCod) \\ tyvarsNames
        _ -> ftvTy ty
