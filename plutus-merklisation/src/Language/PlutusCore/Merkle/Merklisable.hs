{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Language.PlutusCore.Merkle.Merklisable where

import           Codec.Serialise                 (serialise)
import           Crypto.Hash
import qualified Data.ByteArray                  as B
import qualified Data.ByteString.Lazy            as BSL
import qualified Data.Text                       as D
import           Data.Text.Encoding              (encodeUtf8)
import           GHC.Natural                     (Natural)
import qualified Language.PlutusCore             as P
import qualified Language.PlutusCore.Merkle.Type as M

type Hash = Digest SHA256

class Merklisable a where
    merkleHash :: a -> Hash

instance Merklisable [Hash]
    where merkleHash l = hashFinalize $ hashUpdates (hashInit) l

instance Merklisable String where
    merkleHash s = hashWith SHA256 (encodeUtf8 $ D.pack s)

instance Merklisable () where
    merkleHash _ = merkleHash "()"

instance Merklisable Integer where -- Do we need tags here too?
    merkleHash  = merkleHash . show

instance Merklisable Int where
    merkleHash  = merkleHash . show

instance Merklisable GHC.Natural.Natural where
    merkleHash = merkleHash . show

instance Merklisable BSL.ByteString where
    merkleHash = merkleHash . show   -- FIXME

instance Merklisable D.Text where
    merkleHash = merkleHash . D.unpack

instance Merklisable P.Unique where
    merkleHash = merkleHash . P.unUnique


-- We need instances for both P and M for experimental purposes.
-- Here are the instances for P

instance Merklisable ann => Merklisable (P.Name ann) where
    merkleHash (P.Name x str uniq) = merkleHash [merkleHash "Name", merkleHash x, merkleHash str, merkleHash uniq]

instance Merklisable ann => Merklisable (P.TyName ann) where
    merkleHash (P.TyName name) = merkleHash [merkleHash "TyName", merkleHash name]

instance Merklisable P.TypeBuiltin where
    merkleHash = \case
       P.TyByteString -> merkleHash "TyByteString"
       P.TyInteger    -> merkleHash "TyInteger"
       P.TyString     -> merkleHash "TyString"

instance Merklisable ann => Merklisable (P.Kind ann) where
    merkleHash = \case
         P.Type x            -> merkleHash [merkleHash x, merkleHash "*"]
         P.KindArrow x k1 k2 -> merkleHash [merkleHash x, merkleHash k1, merkleHash k2]

-- We need to include the node names (or some other unique thing) in the Merklization here
-- so that eg, you can't replace a TyFun with a TyIfix, or a TyForall with a TyBuiltin.
instance Merklisable ann => Merklisable (P.Type P.TyName ann) where
    merkleHash = \case
      P.TyVar     x tn         -> merkleHash [merkleHash "TyVar",     merkleHash x, merkleHash tn]
      P.TyFun     x ty1 ty2    -> merkleHash [merkleHash "TyFun",     merkleHash x, merkleHash ty1, merkleHash ty2]
      P.TyIFix    x ty1 ty2    -> merkleHash [merkleHash "TyIfix",    merkleHash x, merkleHash ty1, merkleHash ty2]
      P.TyForall  x tn k ty    -> merkleHash [merkleHash "TyForall",  merkleHash x, merkleHash tn, merkleHash k, merkleHash ty]
      P.TyBuiltin x tbi        -> merkleHash [merkleHash "TyBuilitn", merkleHash x, merkleHash tbi]
      P.TyLam     x tn k ty    -> merkleHash [merkleHash "TyLam",     merkleHash x, merkleHash tn,  merkleHash k, merkleHash ty]
      P.TyApp     x ty1 ty2    -> merkleHash [merkleHash "TyApp",     merkleHash x, merkleHash ty1, merkleHash ty2]


instance Merklisable ann => Merklisable (P.Constant ann) where
    merkleHash = \case
      P.BuiltinInt x n  -> merkleHash [merkleHash x, merkleHash "BuiltinInt", merkleHash n]
      P.BuiltinBS  x bs -> merkleHash [merkleHash x, merkleHash "BuiltinBS",  merkleHash bs]
      P.BuiltinStr x s  -> merkleHash [merkleHash x, merkleHash "BuiltinSer", merkleHash s]


-- Now do these

instance Merklisable ann => Merklisable (P.Builtin ann) where
    merkleHash = \case
       P.BuiltinName x name -> merkleHash [merkleHash "BuiltinName", merkleHash x, merkleHash "name"]  -- FIXME
       P.DynBuiltinName x name -> merkleHash [merkleHash "DynBuiltinName", merkleHash x, merkleHash "name"] --FIXME

instance Merklisable ann => Merklisable (P.Term P.TyName P.Name ann) where
    merkleHash = \case
      P.Var      x n         -> merkleHash [merkleHash "Var",      merkleHash x, merkleHash n]
      P.TyAbs    x tn k t    -> merkleHash [merkleHash "TyAbs",    merkleHash x, merkleHash tn, merkleHash k, merkleHash t]
      P.LamAbs   x n ty t    -> merkleHash [merkleHash "LamAbs",   merkleHash x, merkleHash n, merkleHash ty, merkleHash t]
      P.Apply    x t1 t2     -> merkleHash [merkleHash "Apply",    merkleHash x, merkleHash t1, merkleHash t2]
      P.Constant x c         -> merkleHash [merkleHash "Constant", merkleHash x, merkleHash c]
      P.Builtin  x b         -> merkleHash [merkleHash "Builtin",  merkleHash x, merkleHash x, merkleHash b]
      P.TyInst   x t ty      -> merkleHash [merkleHash "TyInst",   merkleHash x, merkleHash t, merkleHash ty]
      P.Unwrap   x t         -> merkleHash [merkleHash "Unwrap",   merkleHash x, merkleHash t]
      P.IWrap    x ty1 ty2 t -> merkleHash [merkleHash "IWrap",    merkleHash x, merkleHash ty1, merkleHash ty2, merkleHash t]
      P.Error    x ty        -> merkleHash [merkleHash "Error",    merkleHash x, merkleHash ty]

instance Merklisable ann => Merklisable (P.Version ann) where
    merkleHash (P.Version x a b c) = merkleHash [merkleHash "Version", merkleHash x, merkleHash a, merkleHash b, merkleHash c]

instance Merklisable ann => Merklisable (P.Program P.TyName P.Name ann) where
    merkleHash (P.Program x version body) = merkleHash [merkleHash "Program", merkleHash x, merkleHash version, merkleHash body]


-- Here are the instances for M.

instance Merklisable ann => Merklisable (M.Kind ann) where
    merkleHash = \case
         M.Type x            -> merkleHash [merkleHash x, merkleHash "*"]
         M.KindArrow x k1 k2 -> merkleHash [merkleHash x, merkleHash k1, merkleHash k2]

-- We need to include the node names (or some other unique thing) in the Merklization here
-- so that eg, you can't replace a TyFun with a TyIfix, or a TyForall with a TyBuiltin.
instance Merklisable ann => Merklisable (M.Type P.TyName ann) where
    merkleHash = \case
      M.TyVar     x tn         -> merkleHash [merkleHash "TyVar",     merkleHash x, merkleHash tn]
      M.TyFun     x ty1 ty2    -> merkleHash [merkleHash "TyFun",     merkleHash x, merkleHash ty1, merkleHash ty2]
      M.TyIFix    x ty1 ty2    -> merkleHash [merkleHash "TyIfix",    merkleHash x, merkleHash ty1, merkleHash ty2]
      M.TyForall  x tn k ty    -> merkleHash [merkleHash "TyForall",  merkleHash x, merkleHash tn, merkleHash k, merkleHash ty]
      M.TyBuiltin x tbi        -> merkleHash [merkleHash "TyBuilitn", merkleHash x, merkleHash tbi]
      M.TyLam     x tn k ty    -> merkleHash [merkleHash "TyLam",     merkleHash x, merkleHash tn,  merkleHash k, merkleHash ty]
      M.TyApp     x ty1 ty2    -> merkleHash [merkleHash "TyApp",     merkleHash x, merkleHash ty1, merkleHash ty2]
      M.TyPruned  _ h          -> h  -- Careful here

instance Merklisable ann => Merklisable (M.Constant ann) where
    merkleHash = \case
      M.BuiltinInt x n  -> merkleHash [merkleHash x, merkleHash "BuiltinInt", merkleHash n]
      M.BuiltinBS  x bs -> merkleHash [merkleHash x, merkleHash "BuiltinBS",  merkleHash bs]
      M.BuiltinStr x s  -> merkleHash [merkleHash x, merkleHash "BuiltinSer", merkleHash s]


-- Now do these

instance Merklisable ann => Merklisable (M.Builtin ann) where
    merkleHash = \case
       M.BuiltinName x name -> merkleHash [merkleHash "BuiltinName", merkleHash x, merkleHash "name"]  -- FIXME
       M.DynBuiltinName x name -> merkleHash [merkleHash "DynBuiltinName", merkleHash x, merkleHash "name"] --FIXME

instance Merklisable ann => Merklisable (M.Term P.TyName P.Name ann) where
    merkleHash = \case
      M.Var      x n         -> merkleHash [merkleHash "Var",      merkleHash x, merkleHash n]
      M.TyAbs    x tn k t    -> merkleHash [merkleHash "TyAbs",    merkleHash x, merkleHash tn, merkleHash k, merkleHash t]
      M.LamAbs   x n ty t    -> merkleHash [merkleHash "LamAbs",   merkleHash x, merkleHash n, merkleHash ty, merkleHash t]
      M.Apply    x t1 t2     -> merkleHash [merkleHash "Apply",    merkleHash x, merkleHash t1, merkleHash t2]
      M.Constant x c         -> merkleHash [merkleHash "Constant", merkleHash x, merkleHash c]
      M.Builtin  x b         -> merkleHash [merkleHash "Builtin",  merkleHash x, merkleHash x, merkleHash b]
      M.TyInst   x t ty      -> merkleHash [merkleHash "TyInst",   merkleHash x, merkleHash t, merkleHash ty]
      M.Unwrap   x t         -> merkleHash [merkleHash "Unwrap",   merkleHash x, merkleHash t]
      M.IWrap    x ty1 ty2 t -> merkleHash [merkleHash "IWrap",    merkleHash x, merkleHash ty1, merkleHash ty2, merkleHash t]
      M.Error    x ty        -> merkleHash [merkleHash "Error",    merkleHash x, merkleHash ty]
      M.Prune    _ h         -> h  -- Careful here.
instance Merklisable ann => Merklisable (M.Program P.TyName P.Name ann) where
    merkleHash (M.Program x version body) = merkleHash [merkleHash "Program", merkleHash x, merkleHash version, merkleHash body]


