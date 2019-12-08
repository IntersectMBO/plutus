{-# LANGUAGE LambdaCase #-}

module Language.PlutusCore.Merkle.Convert
    ( fromCoreProgram
    ) where

import qualified Language.PlutusCore             as P
import qualified Language.PlutusCore.Merkle.Type as M

fromCoreConstant :: P.Constant ann -> M.Constant ann
fromCoreConstant =
    \case
     P.BuiltinInt ann i -> M.BuiltinInt ann i
     P.BuiltinBS  ann b -> M.BuiltinBS  ann b
     P.BuiltinStr ann s -> M.BuiltinStr ann s


fromCoreBuiltin :: P.Builtin ann -> M.Builtin ann
fromCoreBuiltin =
    \case
     P.BuiltinName    ann nm -> M.BuiltinName    ann nm
     P.DynBuiltinName ann nm -> M.DynBuiltinName ann nm


fromCoreKind :: P.Kind ann -> M.Kind ann
fromCoreKind =
    \case
     P.Type ann -> M.Type ann
     P.KindArrow ann k1 k2 -> M.KindArrow ann (fromCoreKind k1) (fromCoreKind k2)

fromCoreType :: P.Type P.TyName ann -> M.Type P.TyName ann
fromCoreType =
    \case
     P.TyVar     ann tn      -> M.TyVar     ann tn
     P.TyFun     ann ty ty'  -> M.TyFun     ann (fromCoreType ty) (fromCoreType ty')
     P.TyIFix    ann ty ty'  -> M.TyIFix    ann (fromCoreType ty) (fromCoreType ty')
     P.TyForall  ann tn k ty -> M.TyForall  ann tn (fromCoreKind k) (fromCoreType ty)
     P.TyBuiltin ann tb      -> M.TyBuiltin ann tb
     P.TyLam     ann tn k ty -> M.TyLam     ann tn (fromCoreKind k) (fromCoreType ty)
     P.TyApp     ann ty ty'  -> M.TyApp     ann (fromCoreType ty) (fromCoreType ty')




fromCoreTerm :: P.Term P.TyName P.Name ann -> M.Term P.TyName P.Name ann
fromCoreTerm =
    \case
     P.Var ann n           -> M.Var      ann n
     P.TyAbs ann tn k t    -> M.TyAbs    ann tn (fromCoreKind k) (fromCoreTerm t)
     P.LamAbs ann n ty t   -> M.LamAbs   ann n (fromCoreType ty) (fromCoreTerm t)
     P.Apply ann t t'      -> M.Apply    ann (fromCoreTerm t) (fromCoreTerm t')
     P.Constant ann c      -> M.Constant ann (fromCoreConstant c)
     P.TyInst ann t ty     -> M.TyInst   ann (fromCoreTerm t) (fromCoreType ty)
     P.Unwrap ann t        -> M.Unwrap   ann (fromCoreTerm t)
     P.IWrap ann pat arg t -> M.IWrap    ann (fromCoreType pat) (fromCoreType arg) (fromCoreTerm t)
     P.Error ann ty        -> M.Error    ann (fromCoreType ty)
     P.Builtin ann bi      -> M.Builtin  ann (fromCoreBuiltin bi)

fromCoreProgram :: P.Program P.TyName P.Name ann -> M.Program P.TyName P.Name ann
fromCoreProgram (P.Program a version body) = M.Program a version (fromCoreTerm body)
