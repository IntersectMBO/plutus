{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
                                ) where

import           Control.Lens
import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable
import           Instances.TH.Lift              ()
import           Language.Haskell.TH.Syntax     (Lift)
import           Language.PlutusCore.Lexer.Type
import qualified Language.PlutusCore.Type       as T
import           PlutusPrelude

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
        T.TyInst _ t _  -> erase t
        T.Unwrap _ t     -> erase t
        T.IWrap _ _ _ t  -> erase t
        T.Error x _      -> Error x


eraseProgram :: T.Program _ty name a -> Program name a
eraseProgram (T.Program ann version body) = Program ann version (erase body)
