{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}







-- | This module defines unification of dependent types.

module Elaboration.Unification where

import Utils.ABT
-- import Utils.Elaborator
import Utils.Pretty
import Utils.Unifier
import PlutusTypes.Type
import Elaboration.Elaborator

import Control.Monad.Except







-- | Equating terms by trivial structural equations.

instance MonadUnify TypeF Elaborator where
  equate (TyCon tycon1 as1) (TyCon tycon2 as2) =
    do unless (tycon1 == tycon2)
         $ throwError $ "Mismatching type constructors "
                     ++ tycon1 ++ " and " ++ tycon2
       unless (length as1 == length as2)
         $ throwError $ "Mismatching type constructor arg lengths between "
                         ++ pretty (In (TyCon tycon1 as1)) ++ " and "
                         ++ pretty (In (TyCon tycon2 as1))
       return $ zipWith
                  Equation
                  (map instantiate0 as1)
                  (map instantiate0 as2)
  equate (Fun a1 b1) (Fun a2 b2) =
    return [ Equation (instantiate0 a1) (instantiate0 a2)
           , Equation (instantiate0 b1) (instantiate0 b2)
           ]
  -- equate (Forall sc1) (Forall sc2) =
  --   do ns <- freshRelTo (names sc1) context
  --      let xs = map (Var . Free) ns
  --      return [ Equation (instantiate sc1 xs) (instantiate sc2 xs) ]
  equate (Comp a1) (Comp a2) =
    return [ Equation (instantiate0 a1) (instantiate0 a2) ]
  equate PlutusInt PlutusInt =
    return []
  equate PlutusFloat PlutusFloat =
    return []
  equate PlutusByteString PlutusByteString =
    return []
  equate l r =
    throwError $ "Cannot unify " ++ pretty (In l) ++ " with " ++ pretty (In r)