{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Erasure.Untyped.Term ( Term (..)
                                , termSubterms
                                , termVars
                                , Value
                                , Program (..)
                                , Constant (..)
                                , Builtin (..)
--                                , BuiltinName (..)
--                                , DynamicBuiltinName (..)
--                                , StagedBuiltinName (..)
                                -- * Helper functions
                                , termLoc
                                -- * Normalized
                                , Normalized (..)
                                , erase
                                , eraseProgram
                                , anonProgram
                                , IntName (..)
                                , nameToIntProgram
                                , deBruijnToIntProgram
                                ) where

import           Codec.CBOR.Decoding
import           Codec.Serialise
import           Control.Lens                 hiding (anon)
import qualified Data.ByteString.Lazy         as BSL
--import           Data.Functor.Foldable
import           Instances.TH.Lift            ()
import           Language.Haskell.TH.Syntax   (Lift)
import qualified Language.PlutusCore.Core     as PLC
import qualified Language.PlutusCore.DeBruijn as D
import qualified Language.PlutusCore.Name     as N
import           PlutusPrelude

termLoc :: Term name a -> a
termLoc (Var l _)      = l
termLoc (Apply l _ _)  = l
termLoc (Constant l _) = l
termLoc (Builtin l _)  = l
termLoc (Error l)      = l
termLoc (LamAbs l _ _) = l

data Builtin a = BuiltinName a PLC.BuiltinName  -- Just copy Builtin and Constant to simplify things
               | DynBuiltinName a PLC.DynamicBuiltinName
               deriving (Functor, Show, Generic, NFData, Lift)

translateBuiltin :: PLC.Builtin a -> Builtin a
translateBuiltin = \case
  PLC.BuiltinName x n    -> BuiltinName x n
  PLC.DynBuiltinName x n -> DynBuiltinName x n

-- | A constant value.
data Constant a = BuiltinInt a Integer
                | BuiltinBS a BSL.ByteString
                | BuiltinStr a String
                deriving (Functor, Show, Generic, NFData, Lift)

translateConstant :: PLC.Constant a -> Constant a
translateConstant = \case
     PLC.BuiltinInt x n -> BuiltinInt x n
     PLC.BuiltinBS x s  -> BuiltinBS x s
     PLC.BuiltinStr x s -> BuiltinStr x s

-- | A 'Term' is a value.
data Term name a = Var a (name a) -- ^ A named variable
                 | LamAbs a (name a) (Term name a)
                 | Apply a (Term name a) (Term name a)
                 | Constant a (Constant a) -- ^ A constant term
                 | Builtin a (Builtin a)
                 | Error a
                   deriving (Functor, Show, Generic, NFData, Lift)

type Value = Term

data Program name ann = Program ann (PLC.Version ann) (Term name ann)
    deriving (Show, Functor, Generic, NFData, Lift)

{-# INLINE termSubterms #-}
-- | Get all the direct child 'Term's of the given 'Term'.
termSubterms :: Traversal' (Term name a) (Term name a)
termSubterms f = \case
    LamAbs x n t -> LamAbs x n <$> f t
    Apply x t1 t2 -> Apply x <$> f t1 <*> f t2
    e@Error {} -> pure e
    v@Var {} -> pure v
    c@Constant {} -> pure c
    b@Builtin {} -> pure b

-- | Get all the direct child 'name a's of the given 'Term' from 'Var's.
termVars :: Traversal' (Term name a) (name a)
termVars f = \case
    Var a n -> Var a <$> f n
    x -> pure x

newtype Normalized a = Normalized { unNormalized :: a }
    deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
    deriving newtype NFData

instance Applicative Normalized where
    pure = Normalized
    Normalized f <*> Normalized x = Normalized $ f x

instance PrettyBy config a => PrettyBy config (Normalized a) where
    prettyBy config (Normalized x) = prettyBy config x


erase :: PLC.Term _tyname name a -> Term name a
erase = \case
        PLC.Var x n        -> Var x n
        PLC.TyAbs _ _ _ t  -> erase t
        PLC.LamAbs x n _ t -> LamAbs x n (erase t)
        PLC.Apply x t1 t2  -> Apply x (erase t1) (erase t2)
        PLC.Constant x c   -> Constant x (translateConstant c)
        PLC.Builtin x b    -> Builtin x (translateBuiltin b)
        PLC.TyInst _ t _   -> erase t
        PLC.Unwrap _ t     -> erase t
        PLC.IWrap _ _ _ t  -> erase t
        PLC.Error x _      -> Error x


eraseProgram :: PLC.Program _ty name a -> Program name a
eraseProgram (PLC.Program ann version body) = Program ann version (erase body)


-- Let's also try getting rid of names

anon :: N.Name ann -> N.Name ann
anon (N.Name ann _str uniq) = N.Name ann "" uniq

anonTn :: N.TyName ann -> N.TyName ann
anonTn (N.TyName n) = N.TyName (anon n)

anonTy :: PLC.Type N.TyName ann -> PLC.Type N.TyName ann
anonTy = \case
      PLC.TyVar x tn         -> PLC.TyVar x (anonTn tn)
      PLC.TyFun x ty ty'     -> PLC.TyFun x (anonTy ty) (anonTy ty')
      PLC.TyIFix x ty ty'    -> PLC.TyIFix x (anonTy ty) (anonTy ty')
      PLC.TyForall x tn k ty -> PLC.TyForall x (anonTn tn) k (anonTy ty)
      PLC.TyBuiltin x tb     -> PLC.TyBuiltin x tb
      PLC.TyLam x tn k ty    -> PLC.TyLam x (anonTn tn) k (anonTy ty)
      PLC.TyApp x ty ty'     -> PLC.TyApp x (anonTy ty) (anonTy ty')


anonTerm :: PLC.Term N.TyName N.Name ann -> PLC.Term N.TyName N.Name ann
anonTerm = \case
           PLC.Var x n          -> PLC.Var x (anon n)
           PLC.TyAbs x tn k e   -> PLC.TyAbs x (anonTn tn) k (anonTerm e)
           PLC.LamAbs x n ty e  -> PLC.LamAbs x (anon n) (anonTy ty) (anonTerm e)
           PLC.Apply x e1 e2    -> PLC.Apply x (anonTerm e1) (anonTerm e2)
           PLC.Constant x c     -> PLC.Constant x c
           PLC.Builtin x b      -> PLC.Builtin x b
           PLC.TyInst x e ty    -> PLC.TyInst x (anonTerm e) (anonTy ty)
           PLC.Unwrap x e       -> PLC.Unwrap x (anonTerm e)
           PLC.IWrap x ty ty' e -> PLC.IWrap x (anonTy ty) (anonTy ty') (anonTerm e)
           PLC.Error x ty       -> PLC.Error x (anonTy ty)

anonProgram :: PLC.Program N.TyName N.Name a -> PLC.Program N.TyName N.Name a
anonProgram (PLC.Program ann version body) = PLC.Program ann version (anonTerm body)


-- Now get rid of names completely, and also annotations in names.
-- It's a bit tricky to do this on the typed syntax because the TyName
-- type there isn't parametric over the name type: it has N.Name built
-- in.  This problem doesn't arise with the untyped AST.

newtype IntName a = IntName Int
instance Serialise (IntName a) where
    encode (IntName n) = encode n
    decode = IntName <$> decodeInt

instance Show (IntName a) where
    show (IntName n) = show n

nameToInt :: N.Name a -> IntName a
nameToInt (N.Name _ _ (N.Unique uniq)) = IntName uniq


nameToIntTerm :: Term N.Name ann -> Term IntName ann
nameToIntTerm = \case
        Var x n        -> Var x (nameToInt n)
        LamAbs x n t   -> LamAbs x (nameToInt n) (nameToIntTerm t)
        Apply x t1 t  -> Apply x (nameToIntTerm t1) (nameToIntTerm t)
        Error x        -> Error x
        Constant x c   -> Constant x c
        Builtin x b    -> Builtin x b

nameToIntProgram :: Program N.Name a -> Program IntName a
nameToIntProgram (Program ann version body) = Program ann version (nameToIntTerm body)

{- To get plc source for the use cases,  add

    --ghc-options: -fplugin-opt  Language.PlutusTx.Plugin:dump-plc

   to plutus-use-cases.cabal (under 'library')and then build
   plutus-use-cases.  This will dump the source to the terminal, along
   with all the other build output. This isn't ideal, but it's a quick
   way to get PLC. The source probably won't compile though (clashes
   with built in names; also plc can't handle extensible builtins (yet).
-}


-- A quick converter from terms using names based on deBruijn indices
-- to ones just using Ints, to see if that makes any difference to
-- compressibility.

deBruijnToInt :: D.DeBruijn ann -> IntName ann
deBruijnToInt (D.DeBruijn _attr _string (D.Index n)) = IntName (fromIntegral n)


deBruijnToIntTerm :: Term D.DeBruijn ann -> Term IntName ann
deBruijnToIntTerm = \case
        Var x n        -> Var x (deBruijnToInt n)
        LamAbs x n t   -> LamAbs x (deBruijnToInt n) (deBruijnToIntTerm t)
        Apply x t1 t   -> Apply x (deBruijnToIntTerm t1) (deBruijnToIntTerm t)
        Error x        -> Error x
        Constant x c   -> Constant x c
        Builtin x b    -> Builtin x b

deBruijnToIntProgram :: Program D.DeBruijn a -> Program IntName a
deBruijnToIntProgram (Program ann version body) = Program ann version (deBruijnToIntTerm body)


