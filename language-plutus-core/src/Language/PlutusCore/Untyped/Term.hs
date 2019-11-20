{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Untyped.Term ( Term (..)
                                , termSubterms
                                , termVars
                                , Value
                                , Program (..)
                                , Constant (..)
                                , Builtin (..)
                                , BuiltinName (..)
                                , DynamicBuiltinName (..)
                                , StagedBuiltinName (..)
                                -- * Base functors
                                , TermF (..)
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

import           Control.Lens                   hiding (anon)
import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable
import           Instances.TH.Lift              ()
import           Language.Haskell.TH.Syntax     (Lift)
import qualified Language.PlutusCore.DeBruijn   as D
import           Language.PlutusCore.Lexer.Type
import qualified Language.PlutusCore.Type       as T
import qualified Language.PlutusCore.Name       as N
import           PlutusPrelude
import           Codec.Serialise
import           Codec.CBOR.Decoding

termLoc :: Term name a -> a
termLoc (Var l _)        = l
termLoc (Apply l _ _)    = l
termLoc (Constant l _)   = l
termLoc (Builtin l _)    = l
termLoc (Error l)        = l
termLoc (LamAbs l _ _)   = l

data Builtin a = BuiltinName a BuiltinName  -- Just copy Builtin and Constant to simplify things
               | DynBuiltinName a DynamicBuiltinName
               deriving (Functor, Show, Eq, Generic, NFData, Lift)

translateBuiltin :: T.Builtin a -> Builtin a
translateBuiltin = \case
  T.BuiltinName x n    -> BuiltinName x n
  T.DynBuiltinName x n -> DynBuiltinName x n
                        
-- | A constant value.
data Constant a = BuiltinInt a Integer
                | BuiltinBS a BSL.ByteString
                | BuiltinStr a String
                deriving (Functor, Show, Eq, Generic, NFData, Lift)

translateConstant :: T.Constant a -> Constant a
translateConstant = \case
     T.BuiltinInt x n -> BuiltinInt x n
     T.BuiltinBS x s  -> BuiltinBS x s
     T.BuiltinStr x s -> BuiltinStr x s
                         
-- | A 'Term' is a value.
data Term name a = Var a (name a) -- ^ A named variable
                 | LamAbs a (name a) (Term name a)
                 | Apply a (Term name a) (Term name a)
                 | Constant a (Constant a) -- ^ A constant term
                 | Builtin a (Builtin a)
                 | Error a
                   deriving (Functor, Show, Eq, Generic, NFData, Lift)

data TermF name a x = VarF a (name a)
                    | LamAbsF a (name a) x
                    | ApplyF a x x
                    | ConstantF a (Constant a)
                    | BuiltinF a (Builtin a)
                    | ErrorF a 
                      deriving (Functor, Traversable, Foldable)

type instance Base (Term name a) = TermF name a

type Value = Term

data Program name ann = Program ann (Version ann) (Term name ann)
    deriving (Show, Eq, Functor, Generic, NFData, Lift)

instance Recursive (Term name a) where
    project (Var x n)           = VarF x n
    project (LamAbs x n t)      = LamAbsF x n t
    project (Apply x t t')      = ApplyF x t t'
    project (Constant x c)      = ConstantF x c
    project (Builtin x bi)      = BuiltinF x bi
    project (Error x)           = ErrorF x

instance Corecursive (Term name a) where
    embed (VarF x n)           = Var x n
    embed (LamAbsF x n t)      = LamAbs x n t
    embed (ApplyF x t t')      = Apply x t t'
    embed (ConstantF x c)      = Constant x c
    embed (BuiltinF x bi)      = Builtin x bi
    embed (ErrorF x)           = Error x

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


erase :: T.Term _tyname name a -> Term name a
erase = \case
        T.Var x n        -> Var x n
        T.TyAbs _ _ _ t  -> erase t
        T.LamAbs x n _ t -> LamAbs x n (erase t)
        T.Apply x t1 t2  -> Apply x (erase t1) (erase t2)
        T.Constant x c   -> Constant x (translateConstant c)
        T.Builtin x b    -> Builtin x (translateBuiltin b)
        T.TyInst _ t _   -> erase t
        T.Unwrap _ t     -> erase t
        T.IWrap _ _ _ t  -> erase t
        T.Error x _      -> Error x


eraseProgram :: T.Program _ty name a -> Program name a
eraseProgram (T.Program ann version body) = Program ann version (erase body)


-- Let's also try getting rid of names

anon :: N.Name ann -> N.Name ann
anon (N.Name ann _str uniq) = N.Name ann "" uniq

anonTn :: N.TyName ann -> N.TyName ann
anonTn (N.TyName n) = N.TyName (anon n) 
                              
anonTy :: T.Type N.TyName ann -> T.Type N.TyName ann
anonTy = \case
      T.TyVar x tn         -> T.TyVar x (anonTn tn)
      T.TyFun x ty ty'     -> T.TyFun x (anonTy ty) (anonTy ty')
      T.TyIFix x ty ty'    -> T.TyIFix x (anonTy ty) (anonTy ty')
      T.TyForall x tn k ty -> T.TyForall x (anonTn tn) k (anonTy ty)
      T.TyBuiltin x tb     -> T.TyBuiltin x tb
      T.TyLam x tn k ty    -> T.TyLam x (anonTn tn) k (anonTy ty)
      T.TyApp x ty ty'     -> T.TyApp x (anonTy ty) (anonTy ty')

                              
anonTerm :: T.Term N.TyName N.Name ann -> T.Term N.TyName N.Name ann
anonTerm = \case
           T.Var x n          -> T.Var x (anon n)
           T.TyAbs x tn k e   -> T.TyAbs x (anonTn tn) k (anonTerm e)
           T.LamAbs x n ty e  -> T.LamAbs x (anon n) (anonTy ty) (anonTerm e)
           T.Apply x e1 e2    -> T.Apply x (anonTerm e1) (anonTerm e2)
           T.Constant x c     -> T.Constant x c
           T.Builtin x b      -> T.Builtin x b
           T.TyInst x e ty    -> T.TyInst x (anonTerm e) (anonTy ty)
           T.Unwrap x e       -> T.Unwrap x (anonTerm e)
           T.IWrap x ty ty' e -> T.IWrap x (anonTy ty) (anonTy ty') (anonTerm e)
           T.Error x ty       -> T.Error x (anonTy ty)

anonProgram :: T.Program N.TyName N.Name a -> T.Program N.TyName N.Name a
anonProgram (T.Program ann version body) = T.Program ann version (anonTerm body)


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
-- to ones just using Ints, to see if that makes any differenc to
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

