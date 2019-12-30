{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}

module Language.PlutusCore.Erasure.Untyped.MkPlc ( TermLike (..)
                                 , embed
                                 , mkIterApp
                                 ) where

import           Prelude                  hiding (error)

import           Language.PlutusCore.Erasure.Untyped.Term

import           Data.List                (foldl')

-- | A final encoding for Term, to allow PLC terms to be used transparently as PIR terms.
class TermLike term name | term -> name where
    var      :: a -> name a -> term a
    lamAbs   :: a -> name a -> term a -> term a
    apply    :: a -> term a -> term a -> term a
    constant :: a -> Constant a -> term a
    builtin  :: a -> Builtin a -> term a
    error    :: a -> term a

instance TermLike (Term name) name where
    var      = Var
    lamAbs   = LamAbs
    apply    = Apply
    constant = Constant
    builtin  = Builtin
    error    = Error

embed :: TermLike term name => Term name a -> term a
embed = \case
    Var a n           -> var a n
    LamAbs a n t      -> lamAbs a n  (embed t)
    Apply a t1 t2     -> apply a (embed t1) (embed t2)
    Constant a c      -> constant a c
    Builtin a bi      -> builtin a bi
    Error a           -> Language.PlutusCore.Erasure.Untyped.MkPlc.error a


-- | Make an iterated application.
mkIterApp
    :: TermLike term tname
    => a
    -> term a -- ^ @f@
    -> [term a] -- ^@[ x0 ... xn ]@
    -> term a -- ^ @[f x0 ... xn ]@
mkIterApp x = foldl' (apply x)
