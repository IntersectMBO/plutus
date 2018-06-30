{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}







-- | This module defines a number of tools for use with elaborators.

module Utils.Elaborator where

import Utils.ABT
import Utils.Vars

import Control.Lens
import Control.Monad.State







type MonadElab s m = MonadState s m





-- | 'getElab' is a mnemonic for looking up the value of a lens on state.

getElab :: MonadState s m => Lens' s a -> m a
getElab = use





-- | 'putElab' is a mnemonic for replacing the value of a lens on state.

putElab :: MonadState s m => Lens' s a -> a -> m ()
putElab = assign





-- | Given a lens that focuses on a list, we can add new elements to the list.

addElab :: MonadState s m => Lens' s [a] -> [a] -> m ()
addElab l xs = l %= (xs ++)





-- | Given a lens that focuses on a list, we can temporarily add new elements
-- to the list for some computation.

extendElab :: MonadState s m => Lens' s [a] -> [a] -> m b -> m b
extendElab l xs m = do oldXs <- getElab l
                       addElab l xs
                       v <- m
                       putElab l oldXs
                       return v





-- | 'removeElab' is a mnemonic for removing values from a list given a lens
-- into that list in the state and a predicate describing the items.

removeElab :: MonadState s m => Lens' s [a] -> (a -> Bool) -> m ()
removeElab l p = do oldXs <- getElab l
                    putElab l (filter (not . p) oldXs)





-- | Given a lens that focuses on a list, we can add new elements to the list
-- for some computation, and then remove some elements that satisfy a
-- predicate.

extendElab' :: MonadState s m
            => Lens' s [a] -> [a] -> (a -> Bool) -> m b -> m b
extendElab' l xs p m = do addElab l xs
                          v <- m
                          removeElab l p
                          return v





-- | Given a lens that focuses on a numeric value, we can increment that value
-- and get back the original. This is useful for name stores to generate
-- globally unique names, for instance.

nextElab :: (Num a, MonadState s m) => Lens' s a -> m a
nextElab l = do i <- getElab l
                putElab l (i+1)
                return i





-- | We can freshen variables relative to any context-like list.

freshRelTo :: MonadState s m
            => [String] -> Lens' s [(FreeVar,a)] -> m [FreeVar]
freshRelTo ns l = do ctx <- getElab l
                     let oldNs = [ n' | (FreeVar n',_) <- ctx ]
                     return $ map FreeVar (freshen oldNs ns)





-- | We can open a scope with fresh names relative to any context-like list.

open :: (MonadElab s m, Functor f, Foldable f)
     => Lens' s [(FreeVar,a)]
     -> Scope f
     -> m ([FreeVar], [String], ABT f)
open l sc =
  do ns <- freshRelTo (names sc) l
     let newVars = [ Var (Free n) | n <- ns ]
         newNames = [ x | FreeVar x <- ns ]
         m = instantiate sc newVars
     return (ns, newNames, m)





openScope :: (Functor f, Foldable f)
          => [(FreeVar,a)] -> Scope f -> ([FreeVar], [String], ABT f)
openScope ctx sc =
  let ns = names sc
      oldNs = [ n' | (FreeVar n',_) <- ctx ]
      freshNs = map FreeVar (freshen oldNs ns)
      newVars = [ Var (Free n) | n <- freshNs ]
      newNames = [ x | FreeVar x <- freshNs ]
      m = instantiate sc newVars
  in (freshNs, newNames, m)