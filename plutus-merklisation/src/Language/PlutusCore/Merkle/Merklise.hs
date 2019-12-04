{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Language.PlutusCore.Merkle.Merklise where

import           Codec.Serialise                        (serialise)
import           Control.Monad
import           Crypto.Hash
import           Data.Functor.Foldable
import qualified Data.Set
import qualified Language.PlutusCore                    as P
import           Language.PlutusCore.Merkle.Merklisable
import           Language.PlutusCore.Merkle.Type

{- Numbering nodes.  We replace the annotations in an AST with unique
   Integers.  We do this by passing in a tree containing all the
   natural numbers, using the number at the root to number the current
   node and left and right subtrees to number subterms etc.  This is a
   bit profligate, but has the advantage of being purely functional. }
-}

data Numbers = Numbers {first::Integer, left::Numbers, right:: Numbers}

makeNumbers :: Integer -> Numbers
makeNumbers n = Numbers n (makeNumbers $ 2*n) (makeNumbers $ 2*n+1)

nats :: Numbers
nats = makeNumbers 0 --- An infinite tree containing each natural number exactly once

numberName :: Numbers -> P.Name a -> P.Name Integer
numberName numbers (P.Name x s u) = P.Name (first numbers) s u

numberType :: Numbers -> Type P.TyName a -> Type P.TyName Integer
numberType (Numbers q l r) =
    \case
      TyVar _ tn         -> TyVar q (numberTyname l tn)
      TyFun _ ty ty'     -> TyFun q (numberType l ty) (numberType r ty')
      TyIFix _ ty ty'    -> TyIFix q (numberType l ty) (numberType r ty')
      TyForall _ tn k ty -> TyForall q (numberTyname (left l) tn) (numberKind (right l) k) (numberType r ty)
      TyBuiltin _ tb     -> TyBuiltin q tb
      TyLam _ tn k ty    -> TyLam q (numberTyname (left l) tn) (numberKind (right l) k) (numberType r ty)
      TyApp _ ty ty'     -> TyApp q (numberType l ty) (numberType r ty')
      TyPruned _ h       -> TyPruned q h

numberConstant :: Numbers -> Constant a -> Constant Integer
numberConstant (Numbers q _ _) =
    \case
     BuiltinInt _ n -> BuiltinInt q n
     BuiltinBS _ s  -> BuiltinBS q s
     BuiltinStr _ s -> BuiltinStr q s

numberBuiltin :: Numbers -> Builtin a -> Builtin Integer
numberBuiltin (Numbers q _ _)  =
    \case
     BuiltinName _ n    -> BuiltinName q n
     DynBuiltinName _ n -> DynBuiltinName q n


numberTyname :: Numbers -> P.TyName a -> P.TyName Integer
numberTyname numbers (P.TyName n) = P.TyName (numberName numbers n)

numberKind :: Numbers -> Kind a -> Kind Integer
numberKind (Numbers q l r) =
    \case
     Type _            -> Type q
     KindArrow _ k1 k2 -> KindArrow q (numberKind l k1) (numberKind r k2)

numberTerm :: Numbers -> Term P.TyName P.Name a -> Term P.TyName P.Name Integer
numberTerm (Numbers q l r) =
    \case
      Var _ n          -> Var      q (numberName l n)
      LamAbs _ n ty t  -> LamAbs   q (numberName l n) (numberType (left l) ty) (numberTerm r t)
      TyInst _ t ty    -> TyInst   q (numberTerm l t) (numberType r ty)
      IWrap _ ty1 ty t -> IWrap    q (numberType (left l) ty1) (numberType (right l) ty) (numberTerm l t)
      TyAbs _ tn k t   -> TyAbs    q (numberTyname (left l) tn) (numberKind (right l) k) (numberTerm r t)
      Apply _ t1 t2    -> Apply    q (numberTerm l t1) (numberTerm r t2)
      Unwrap _ t       -> Unwrap   q (numberTerm l t)
      Error _ ty       -> Error    q (numberType l ty)
      Constant _ c     -> Constant q (numberConstant l c)
      Builtin _ b      -> Builtin  q (numberBuiltin l b)
      Prune _ h        -> Prune    q h

numberVersion :: Numbers -> P.Version a -> P.Version Integer
numberVersion (Numbers q _ _) (P.Version _ a b c) = P.Version q a b c

numberProgram :: Program P.TyName P.Name a -> Program P.TyName P.Name Integer
numberProgram = numProg nats
    where numProg (Numbers q l r) (Program _ v t) = Program q (numberVersion l v) (numberTerm r t)


{- Pruning unused nodes.  While we're at it, let's convert numeric annotations back to units. -}

unannotateName :: P.Name a -> P.Name ()
unannotateName (P.Name _ s u) = P.Name () s u

unannotateConstant :: Constant a -> Constant ()
unannotateConstant =
    \case
     BuiltinInt _ n -> BuiltinInt () n
     BuiltinBS _ s  -> BuiltinBS () s
     BuiltinStr _ s -> BuiltinStr () s

unannotateBuiltin :: Builtin a -> Builtin ()
unannotateBuiltin =
    \case
     BuiltinName _ n    -> BuiltinName () n
     DynBuiltinName _ n -> DynBuiltinName () n


unannotateTyname :: P.TyName a -> P.TyName ()
unannotateTyname (P.TyName n) = P.TyName (unannotateName n)

unannotateKind :: Kind a -> Kind ()
unannotateKind =
    \case
     Type _            -> Type ()
     KindArrow _ k1 k2 -> KindArrow () (unannotateKind k1) (unannotateKind k2)

unannotateType :: Type P.TyName Integer -> Type P.TyName ()
unannotateType =
    \case
      TyVar _ tn         -> TyVar () (unannotateTyname tn)
      TyFun _ ty ty'     -> TyFun () (unannotateType ty) (unannotateType ty')
      TyIFix _ ty ty'    -> TyIFix () (unannotateType ty) (unannotateType ty')
      TyForall _ tn k ty -> TyForall () (unannotateTyname tn) (unannotateKind k) (unannotateType ty)
      TyBuiltin _ tb     -> TyBuiltin () tb
      TyLam _ tn k ty    -> TyLam () (unannotateTyname tn) (unannotateKind k) (unannotateType ty)
      TyApp _ ty ty'     -> TyApp () (unannotateType ty) (unannotateType ty')
      TyPruned _ h       -> TyPruned () h

unannotateTerm :: Term P.TyName P.Name Integer -> Term P.TyName P.Name ()
unannotateTerm = \case
      Var _ n          -> Var      () (unannotateName n)
      LamAbs _ n ty t  -> LamAbs   () (unannotateName n) (unannotateType ty) (unannotateTerm t)
      TyInst _ t ty    -> TyInst   () (unannotateTerm t) (unannotateType ty)
      IWrap _ ty1 ty t -> IWrap    () (unannotateType ty1) (unannotateType ty) (unannotateTerm t)
      TyAbs _ tn k t   -> TyAbs    () (unannotateTyname tn) (unannotateKind k) (unannotateTerm t)
      Apply _ t1 t2    -> Apply    () (unannotateTerm t1) (unannotateTerm t2)
      Unwrap _ t       -> Unwrap   () (unannotateTerm t)
      Error _ ty       -> Error    () (unannotateType ty)
      Constant _ c     -> Constant () (unannotateConstant c)
      Builtin _ b      -> Builtin  () (unannotateBuiltin b)
      Prune _ h        -> Prune    () h

type NumSet = Data.Set.Set Integer

typeId :: Type P.TyName Integer -> Integer
typeId =
    \case
      TyVar q _          -> q
      TyFun q _   _      -> q
      TyIFix q _ _       -> q
      TyForall q _ _ _   -> q
      TyBuiltin q _      -> q
      TyLam q _ _ _      -> q
      TyApp q _ _        -> q
      TyPruned q _       -> q


pruneType :: NumSet -> Type P.TyName Integer -> Type P.TyName ()
pruneType used ty0 =
    if not $ Data.Set.member (typeId ty0) used
    then TyPruned () (merkleHash (unannotateType ty0)) -- This is why we need unannotateType
    else case ty0 of
      TyVar _ tn         -> TyVar () (unannotateTyname tn)
      TyFun _ ty ty'     -> TyFun () (pruneType used ty) (pruneType used ty')
      TyIFix _ ty ty'    -> TyIFix () (pruneType used ty) (pruneType used ty')
      TyForall _ tn k ty -> TyForall () (unannotateTyname tn) (unannotateKind k) (pruneType used ty)
      TyBuiltin _ tb     -> TyBuiltin () tb
      TyLam _ tn k ty    -> TyLam () (unannotateTyname tn) (unannotateKind k) (pruneType used ty)
      TyApp _ ty ty'     -> TyApp () (pruneType used ty) (pruneType used ty')
      TyPruned _ h       -> TyPruned () h

termId :: Term P.TyName P.Name Integer -> Integer
termId =
    \case
     Var q _          -> q
     LamAbs q _ _ _   -> q
     TyInst q _ _     -> q
     IWrap q _ _ _    -> q
     TyAbs q _ _ _    -> q
     Apply q _ _      -> q
     Unwrap q _       -> q
     Error q _        -> q
     Constant q _     -> q
     Builtin q _      -> q
     Prune q _        -> q


pruneTerm :: NumSet -> Term P.TyName P.Name Integer -> Term P.TyName P.Name ()
pruneTerm used t0 =
    if not $ Data.Set.member (termId t0) used
    then Prune () (merkleHash (unannotateTerm t0))  -- This is why we need unannotateTerm
    else case t0 of
      Var _ n          -> Var      () (unannotateName n)
      LamAbs _ n ty t  -> LamAbs   () (unannotateName n) (pruneType used ty) (pruneTerm used t)
      TyInst _ t ty    -> TyInst   () (pruneTerm used t) (pruneType used ty)
      IWrap _ ty1 ty t -> IWrap    () (pruneType used ty1) (pruneType used ty) (pruneTerm used t)
      TyAbs _ tn k t   -> TyAbs    () (unannotateTyname tn) (unannotateKind k) (pruneTerm used t)
      Apply _ t1 t2    -> Apply    () (pruneTerm used t1) (pruneTerm used t2)
      Unwrap _ t       -> Unwrap   () (pruneTerm used t)
      Error _ ty       -> Error    () (pruneType used ty)
      Constant _ c     -> Constant () (unannotateConstant c)
      Builtin _ b      -> Builtin  () (unannotateBuiltin b)
      Prune _ h        -> Prune    () h -- Really? We shouldn't be seeing this again

pruneVersion :: P.Version a -> P.Version ()
pruneVersion (P.Version _ a b c) = P.Version () a b c

pruneProgram :: Data.Set.Set Integer -> Program P.TyName P.Name Integer -> Program P.TyName P.Name ()
pruneProgram used (Program _ v t) = Program () (pruneVersion v) (pruneTerm used t)


