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
                                , removeNameStrings
                                , IntName (..)
                                , StringlessName (..)
                                , StringlessTyName (..)
                                , nameToIntProgram
                                , deBruijnToIntProgram
                                , PLC.BuiltinName
                                , PLC.DynamicBuiltinName
                                , PLC.Version
                                ) where

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import           Control.Lens                 hiding (anon)
import           Crypto.Hash
import qualified Data.ByteString.Lazy         as BSL
--import           Data.Functor.Foldable
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
termLoc (Prune l _)    = l

data Builtin a = BuiltinName a PLC.BuiltinName  -- Just copy Builtin and Constant to simplify things
               | DynBuiltinName a PLC.DynamicBuiltinName
               deriving (Functor, Show, Generic, NFData)

translateBuiltin :: PLC.Builtin a -> Builtin a
translateBuiltin = \case
  PLC.BuiltinName x n    -> BuiltinName x n
  PLC.DynBuiltinName x n -> DynBuiltinName x n

-- | A constant value.
data Constant a = BuiltinInt a Integer
                | BuiltinBS a BSL.ByteString
                | BuiltinStr a String
                deriving (Functor, Show, Generic, NFData)

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
                 | Prune a (Digest SHA256)
                   deriving (Functor, Show, Generic, NFData)

type Value = Term

data Program name ann = Program ann (PLC.Version ann) (Term name ann)
                        deriving (Show, Functor, Generic, NFData)

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
    p@Prune {} -> pure p

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


-- Some functions for altering names in typed programs

changeNamesTy :: (tn1 ann -> tn2 ann) -> PLC.Type tn1 ann -> PLC.Type tn2 ann
changeNamesTy g = \case
      PLC.TyVar x tn         -> PLC.TyVar x (g tn)
      PLC.TyFun x ty ty'     -> PLC.TyFun x (changeNamesTy g ty) (changeNamesTy g ty')
      PLC.TyIFix x ty ty'    -> PLC.TyIFix x (changeNamesTy g ty) (changeNamesTy g ty')
      PLC.TyForall x tn k ty -> PLC.TyForall x (g tn) k (changeNamesTy g ty)
      PLC.TyBuiltin x tb     -> PLC.TyBuiltin x tb
      PLC.TyLam x tn k ty    -> PLC.TyLam x (g tn) k (changeNamesTy g ty)
      PLC.TyApp x ty ty'     -> PLC.TyApp x (changeNamesTy g ty) (changeNamesTy g ty')

changeNamesTerm ::  (n1 ann -> n2 ann) -> (tn1 ann -> tn2 ann) -> PLC.Term tn1 n1 ann -> PLC.Term tn2 n2 ann
changeNamesTerm f g = \case
           PLC.Var x n          -> PLC.Var x (f n)
           PLC.TyAbs x tn k e   -> PLC.TyAbs x (g tn) k (changeNamesTerm f g e)
           PLC.LamAbs x n ty e  -> PLC.LamAbs x (f n) (changeNamesTy g ty) (changeNamesTerm f g e)
           PLC.Apply x e1 e2    -> PLC.Apply x (changeNamesTerm f g e1) (changeNamesTerm f g e2)
           PLC.Constant x c     -> PLC.Constant x c
           PLC.Builtin x b      -> PLC.Builtin x b
           PLC.TyInst x e ty    -> PLC.TyInst x (changeNamesTerm f g e) (changeNamesTy g ty)
           PLC.Unwrap x e       -> PLC.Unwrap x (changeNamesTerm f g e)
           PLC.IWrap x ty ty' e -> PLC.IWrap x (changeNamesTy g ty) (changeNamesTy g ty') (changeNamesTerm f g e)
           PLC.Error x ty       -> PLC.Error x (changeNamesTy g ty)

-- Map f over names, g over type names
changeNamesProgram :: (n1 ann -> n2 ann) -> (tn1 ann -> tn2 ann) -> PLC.Program tn1 n1 ann -> PLC.Program tn2  n2 ann
changeNamesProgram f g (PLC.Program ann version body) = PLC.Program ann version (changeNamesTerm f g body)


-- Replace names with empty strings in typed programs
anonProgram :: PLC.Program N.TyName N.Name ann -> PLC.Program N.TyName N.Name ann
anonProgram =
    changeNamesProgram anon anonTy
        where anon (N.Name ann _ u) = N.Name ann "" u
              anonTy (N.TyName n) = N.TyName (anon n)


-- Names with no string ids
data StringlessName ann = StringlessName
    { nameAttribute :: ann
    , nameUnique    :: N.Unique -- ^ A 'Unique' assigned to the name, allowing for cheap comparisons in the compiler.
    } deriving (Eq, Ord, Show, Functor, Generic, NFData)

newtype StringlessTyName ann = StringlessTyName { unTyName :: StringlessName ann }
    deriving (Show, Generic)
    deriving newtype (Eq, Ord, Functor, NFData)

removeNameStrings :: PLC.Program N.TyName N.Name ann -> PLC.Program StringlessTyName StringlessName ann
removeNameStrings = changeNamesProgram f g
              where f (N.Name ann _ u) = StringlessName ann u
                    g (N.TyName n) = StringlessTyName (f n)


-- Changing names in untyped code

changeNamesUntypedTerm :: (name1 ann -> name2 ann) -> Term name1 ann -> Term name2 ann
changeNamesUntypedTerm f = \case
        Var x n        -> Var x (f n)
        LamAbs x n t   -> LamAbs x (f n) (changeNamesUntypedTerm f t)
        Apply x t1 t2   -> Apply x (changeNamesUntypedTerm f t1) (changeNamesUntypedTerm f t2)
        Error x        -> Error x
        Constant x c   -> Constant x c
        Builtin x b    -> Builtin x b
        Prune x h      -> Prune x h
-- NOTE: Changing names will mess up the Merkle hashes, but that
-- doesn't matter too much for the purposes of this code.

changeNamesUntyped :: (name1 ann -> name2 ann) -> Program name1 ann -> Program name2 ann
changeNamesUntyped f (Program ann version body) = Program ann version (changeNamesUntypedTerm f body)


-- Names without strings and without annotations: essentially only Uniques

newtype IntName a = IntName Int
instance Serialise (IntName a) where
    encode (IntName n) = encode n
    decode = IntName <$> decodeInt

instance Show (IntName a) where
    show (IntName n) = show n

nameToInt :: N.Name a -> IntName a
nameToInt (N.Name _ _ (N.Unique uniq)) = IntName uniq

nameToIntProgram :: Program N.Name a -> Program IntName a
nameToIntProgram = changeNamesUntyped nameToInt


{- To get plc source for the use cases,  add

    --ghc-options: -fplugin-opt  Language.PlutusTx.Plugin:dump-plc

   to plutus-use-cases.cabal (under 'library')and then build
   plutus-use-cases.  This will dump the source to the terminal, along
   with all the other build output. This isn't ideal, but it's a quick
   way to get PLC. The source probably won't compile though (clashes
   with built in names; also plc can't handle extensible builtins (yet)).
-}


-- A quick converter from terms using names based on deBruijn indices
-- to ones just using Ints, to see if that makes any difference to
-- compressibility.

deBruijnToInt :: D.DeBruijn ann -> IntName ann
deBruijnToInt (D.DeBruijn _attr _string (D.Index n)) = IntName (fromIntegral n)


deBruijnToIntProgram :: Program D.DeBruijn a -> Program IntName a
deBruijnToIntProgram = changeNamesUntyped deBruijnToInt


