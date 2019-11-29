{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Merkle where

import           Codec.Serialise         (serialise)
import           Crypto.Hash
import qualified Language.PlutusCore     as P
import qualified Language.PlutusCore.Merkle.Type    as M
import qualified Data.ByteString.Lazy    as BSL
import           Data.Text.Encoding      (encodeUtf8)
import qualified Data.Text as D
import qualified Data.ByteArray as B
import           GHC.Natural             (Natural)    

type Hash = Digest SHA256

class Merklisable a where
    merklise :: a -> Hash

instance Merklisable [Hash]
    where merklise l = hashFinalize $ hashUpdates (hashInit) l
                
instance Merklisable String where
    merklise s = hashWith SHA256 (encodeUtf8 $ D.pack s)

instance Merklisable () where
    merklise _ = merklise "()"

instance Merklisable Integer where -- Do we need tags here too?
    merklise  = merklise . show

instance Merklisable Int where
    merklise  = merklise . show

instance Merklisable GHC.Natural.Natural where
    merklise = merklise . show

instance Merklisable BSL.ByteString where
    merklise = merklise . show   -- FIXME
                
instance Merklisable D.Text where
    merklise = merklise . D.unpack

instance Merklisable P.Unique where
    merklise = merklise . P.unUnique

instance Merklisable ann => Merklisable (P.Name ann) where
    merklise (P.Name x str uniq) = merklise [merklise "Name", merklise x, merklise str, merklise uniq]
    
instance Merklisable ann => Merklisable (P.TyName ann) where
    merklise (P.TyName name) = merklise [merklise "TyName", merklise name]
                 
instance Merklisable P.TypeBuiltin where
    merklise = \case
       P.TyByteString -> merklise "TyByteString"
       P.TyInteger    -> merklise "TyInteger"
       P.TyString     -> merklise "TyString"

instance Merklisable ann => Merklisable (P.Kind ann) where
    merklise = \case
         P.Type x            -> merklise [merklise x, merklise "*"]
         P.KindArrow x k1 k2 -> merklise [merklise x, merklise k1, merklise k2]

-- We need to include the node names (or some other unique thing) in the Merklization here
-- so that eg, you can't replace a TyFun with a TyIfix, or a TyForall with a TyBuiltin.
instance Merklisable ann => Merklisable (P.Type P.TyName ann) where
    merklise = \case
      P.TyVar     x tn         -> merklise [merklise "TyVar",     merklise x, merklise tn]
      P.TyFun     x ty1 ty2    -> merklise [merklise "TyFun",     merklise x, merklise ty1, merklise ty2]
      P.TyIFix    x ty1 ty2    -> merklise [merklise "TyIfix",    merklise x, merklise ty1, merklise ty2]
      P.TyForall  x tn k ty    -> merklise [merklise "TyForall",  merklise x, merklise tn, merklise k, merklise ty]
      P.TyBuiltin x tbi        -> merklise [merklise "TyBuilitn", merklise x, merklise tbi]
      P.TyLam     x tn k ty    -> merklise [merklise "TyLam",     merklise x, merklise tn,  merklise k, merklise ty]
      P.TyApp     x ty1 ty2    -> merklise [merklise "TyApp",     merklise x, merklise ty1, merklise ty2]


instance Merklisable ann => Merklisable (P.Constant ann) where
    merklise = \case
      P.BuiltinInt x n  -> merklise [merklise x, merklise "BuiltinInt", merklise n]
      P.BuiltinBS  x bs -> merklise [merklise x, merklise "BuiltinBS",  merklise bs]
      P.BuiltinStr x s  -> merklise [merklise x, merklise "BuiltinSer", merklise s]


-- Now do these
                           
instance Merklisable ann => Merklisable (P.Builtin ann) where
    merklise = \case
       P.BuiltinName x name -> merklise [merklise "BuiltinName", merklise x, merklise "name"]  -- FIXME
       P.DynBuiltinName x name -> merklise [merklise "DynBuiltinName", merklise x, merklise "name"] --FIXME

instance Merklisable ann => Merklisable (P.Term P.TyName P.Name ann) where
    merklise = \case
      P.Var      x n         -> merklise [merklise "Var",      merklise x, merklise n]
      P.TyAbs    x tn k t    -> merklise [merklise "TyAbs",    merklise x, merklise tn, merklise k, merklise t]
      P.LamAbs   x n ty t    -> merklise [merklise "LamAbs",   merklise x, merklise n, merklise ty, merklise t]
      P.Apply    x t1 t2     -> merklise [merklise "Apply",    merklise x, merklise t1, merklise t2]
      P.Constant x c         -> merklise [merklise "Constant", merklise x, merklise c]
      P.Builtin  x b         -> merklise [merklise "Builtin",  merklise x, merklise x, merklise b]
      P.TyInst   x t ty      -> merklise [merklise "TyInst",   merklise x, merklise t, merklise ty]
      P.Unwrap   x t         -> merklise [merklise "Unwrap",   merklise x, merklise t]
      P.IWrap    x ty1 ty2 t -> merklise [merklise "IWrap",    merklise x, merklise ty1, merklise ty2, merklise t]
      P.Error    x ty        -> merklise [merklise "Error",    merklise x, merklise ty]

instance Merklisable ann => Merklisable (P.Version ann) where
    merklise (P.Version x a b c) = merklise [merklise "Version", merklise x, merklise a, merklise b, merklise c]
    
instance Merklisable ann => Merklisable (P.Program P.TyName P.Name ann) where
    merklise (P.Program x version body) = merklise [merklise "Program", merklise x, merklise version, merklise body]


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
merkliseType ty = M.TyPruned (P.tyLoc ty) (merklise ty)
                
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
