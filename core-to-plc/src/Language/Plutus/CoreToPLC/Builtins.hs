{-# LANGUAGE OverloadedStrings #-}
-- | Functions for working with PLC builtins.
module Language.Plutus.CoreToPLC.Builtins where

import           Language.Plutus.CoreToPLC.Laziness

import           GHC.Natural
import qualified Language.PlutusCore                as PLC
import           Language.PlutusCore.Quote

{- Note [Spec booleans and Scott booleans]
Annoyingly, the spec version of booleans bakes in the laziness of the branches,
i.e. has type
forall a . (() -> a) -> (() -> a) -> a
Our booleans converted from Haskell's Bool have type
forall a . a -> a -> a
because we insert the laziness when we do case expressions.

So we need to be able to turn the spec's booleans into our booleans.
-}

-- See Note [Spec booleans and Scott booleans]
specBoolToScottBool :: MonadQuote m => PLC.Term PLC.TyName PLC.Name () -> m (PLC.Term PLC.TyName PLC.Name ())
specBoolToScottBool b = do
    n <- liftQuote $ freshTyName () "Bool_match_out"
    let outTy = PLC.TyVar () n
    let instantiated = PLC.TyInst () b outTy
    a1 <- liftQuote $ freshName () "arg1"
    a2 <- liftQuote $ freshName () "arg2"
    arg1 <- delay $ PLC.Var () a1
    arg2 <- delay $ PLC.Var () a1
    pure $ PLC.TyAbs () n (PLC.Type ()) $ PLC.LamAbs () a1 outTy $ PLC.LamAbs () a2 outTy $ PLC.Apply () (PLC.Apply () instantiated arg1) arg2

binarySpecBoolFunToScottBoolFun :: MonadQuote m => PLC.Type PLC.TyName () -> PLC.Term PLC.TyName PLC.Name () -> m (PLC.Term PLC.TyName PLC.Name ())
binarySpecBoolFunToScottBoolFun ty f = do
    n1 <- liftQuote $ freshName () "arg1"
    n2 <- liftQuote $ freshName () "arg2"
    inner <- specBoolToScottBool $ PLC.Apply () (PLC.Apply () f (PLC.Var () n1)) (PLC.Var () n2)
    pure $ PLC.LamAbs () n1 ty $ PLC.LamAbs () n2 ty inner

haskellIntSize :: Natural
haskellIntSize = 64

haskellBSSize :: Natural
haskellBSSize = 64

instSize :: Natural -> PLC.Term tyname name () -> PLC.Term tyname name ()
instSize n t = PLC.TyInst () t (PLC.TyInt () n)

appSize :: Natural -> PLC.Type tyname () -> PLC.Type tyname ()
appSize n t = PLC.TyApp () t (PLC.TyInt () n)

mkConstant :: PLC.BuiltinName -> PLC.Term tyname name ()
mkConstant n = PLC.Constant () $ PLC.BuiltinName () n

mkIntFun :: MonadQuote m => PLC.BuiltinName -> m (PLC.Term PLC.TyName PLC.Name ())
mkIntFun name = pure $ instSize haskellIntSize (mkConstant name)

mkIntRel :: MonadQuote m => PLC.BuiltinName -> m (PLC.Term PLC.TyName PLC.Name ())
mkIntRel name = do
    let intTy = appSize haskellIntSize (PLC.TyBuiltin () PLC.TyInteger)
    binarySpecBoolFunToScottBoolFun intTy $ instSize haskellIntSize (mkConstant name)

mkBsRel :: MonadQuote m => PLC.BuiltinName -> m (PLC.Term PLC.TyName PLC.Name ())
mkBsRel name = do
    let bsTy = appSize haskellBSSize (PLC.TyBuiltin () PLC.TyByteString)
    binarySpecBoolFunToScottBoolFun bsTy $ instSize haskellBSSize (mkConstant name)
