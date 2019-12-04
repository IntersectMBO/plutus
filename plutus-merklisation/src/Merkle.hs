{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Merkle where

import           Codec.Serialise                        (serialise)
import           Crypto.Hash
import qualified Data.ByteArray                         as B
import qualified Data.ByteString.Lazy                   as BSL
import qualified Data.Text                              as D
import           Data.Text.Encoding                     (encodeUtf8)
import           GHC.Natural                            (Natural)
import qualified Language.PlutusCore                    as P
import           Language.PlutusCore.Merkle.Merklisable (Merklisable, merkleHash)
import qualified Language.PlutusCore.Merkle.Type        as M

--- Merklise types away

translateKind :: P.Kind ann -> M.Kind ann
translateKind = \case
         P.Type x            -> M.Type x
         P.KindArrow x k1 k2 -> M.KindArrow x (translateKind k1) (translateKind k2)

translateBuiltin :: P.Builtin ann -> M.Builtin ann
translateBuiltin = \case
  P.BuiltinName x n    -> M.BuiltinName x n
  P.DynBuiltinName x n -> M.DynBuiltinName x n

translateConstant :: P.Constant ann -> M.Constant ann
translateConstant = \case
     P.BuiltinInt x n -> M.BuiltinInt x n
     P.BuiltinBS x s  -> M.BuiltinBS x s
     P.BuiltinStr x s -> M.BuiltinStr x s



merkliseType :: Merklisable ann => P.Type P.TyName ann -> M.Type P.TyName ann
merkliseType ty = M.TyPruned (P.tyLoc ty) (merkleHash ty)

merkliseTypes :: Merklisable ann => P.Term P.TyName P.Name ann -> M.Term P.TyName P.Name ann
merkliseTypes = \case
      P.Var      x n         -> M.Var      x n
      P.TyAbs    x tn k t    -> M.TyAbs    x tn (translateKind k) (merkliseTypes t)
      P.LamAbs   x n ty t    -> M.LamAbs   x n (merkliseType ty) (merkliseTypes t)
      P.Apply    x t1 t2     -> M.Apply    x (merkliseTypes t1) (merkliseTypes t2)
      P.Constant x c         -> M.Constant x (translateConstant c)
      P.Builtin  x b         -> M.Builtin  x (translateBuiltin b)
      P.TyInst   x t ty      -> M.TyInst   x (merkliseTypes t) (merkliseType ty)
      P.Unwrap   x t         -> M.Unwrap   x (merkliseTypes t)
      P.IWrap    x ty1 ty2 t -> M.IWrap    x (merkliseType ty1) (merkliseType ty2) (merkliseTypes t)
      P.Error    x ty        -> M.Error    x (merkliseType ty)



merkliseProgramTypes :: Merklisable ann => P.Program P.TyName P.Name ann -> M.Program P.TyName P.Name ann
merkliseProgramTypes (P.Program x version body) = M.Program x version (merkliseTypes body)


{- Problem: Digests have type ByteArrayAccess, so we can hash them (again).
   We'd like to concatenate Digests then hash them, so we can generate a digest
   involving the children of a node.  Now we wave

       class (Eq ba, Ord ba, Monoid ba, ByteArrayAccess ba) => ByteArray ba

   and ByteArray does have concatenation.  Digest has Eq and Ord, but not Monoid.

   We'd need an mempty for Digest, which seems improbable.
-}
