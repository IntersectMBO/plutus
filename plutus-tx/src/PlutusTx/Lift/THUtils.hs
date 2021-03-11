{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
module PlutusTx.Lift.THUtils where

import           PlutusIR
import           PlutusIR.Compiler.Names

import           PlutusCore.Quote

import           Control.Monad

import qualified Data.Text                    as T

import qualified Language.Haskell.TH          as TH
import qualified Language.Haskell.TH.Datatype as TH
import qualified Language.Haskell.TH.Syntax   as TH

-- | Very nearly the same as 'TH.showName', but doesn't print uniques, since we don't need to
-- incorporate them into our names.
showName :: TH.Name -> T.Text
showName n = T.pack $ case n of
    TH.Name occ TH.NameS         -> TH.occString occ
    TH.Name occ (TH.NameQ m)     -> TH.modString m ++ "." ++ TH.occString occ
    TH.Name occ (TH.NameG _ _ m) -> TH.modString m ++ "." ++ TH.occString occ
    TH.Name occ (TH.NameU _)     -> TH.occString occ
    TH.Name occ (TH.NameL _)     -> TH.occString occ

-- | Normalize a type, in particular getting rid of things like 'TH.ListT' in favour of applications of the actual name.
normalizeType :: TH.Type -> TH.Type
normalizeType = \case
    TH.ForallT b c t       -> TH.ForallT b c (normalizeType t)
    TH.AppT t1 t2          -> TH.AppT (normalizeType t1) (normalizeType t2)
    TH.SigT t _            -> normalizeType t
    TH.InfixT t1 n t2      -> TH.ConT n `TH.AppT` normalizeType t1 `TH.AppT` normalizeType t2
    TH.UInfixT t1 n t2     -> TH.ConT n `TH.AppT` normalizeType t1 `TH.AppT` normalizeType t2
    TH.ParensT t           -> normalizeType t
    TH.ListT               -> TH.ConT ''[]
    TH.TupleT arity        -> TH.ConT (TH.tupleTypeName arity)
    TH.UnboxedTupleT arity -> TH.ConT (TH.unboxedTupleTypeName arity)
    TH.UnboxedSumT arity   -> TH.ConT (TH.unboxedSumTypeName arity)
    -- some of this stuff probably should be normalized (like tuples) but I don't know quite what to do
    t                      -> t

requireExtension :: TH.Extension -> TH.Q ()
requireExtension ext = do
    enabled <- TH.isExtEnabled ext
    unless enabled $ fail $ "Extension must be enabled: " ++ show ext

mkTyVarDecl :: (MonadQuote m) => TH.Name -> Kind () -> m (TH.Name, TyVarDecl TyName ())
mkTyVarDecl name kind = do
    tyName <- safeFreshTyName $ showName name
    pure (name, TyVarDecl () tyName kind)

isNewtype :: TH.DatatypeInfo -> Bool
isNewtype TH.DatatypeInfo{TH.datatypeVariant=variant} = case variant of
    TH.Newtype -> True
    _          -> False

-- | "Safe" wrapper around 'TH.listE' for typed TH.
tyListE :: [TH.TExpQ a] -> TH.TExpQ [a]
tyListE texps = TH.unsafeTExpCoerce [| $(TH.listE (fmap TH.unTypeQ texps)) |]
