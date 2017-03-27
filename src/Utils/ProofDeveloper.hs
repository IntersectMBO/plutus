{-# OPTIONS -Wall #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Utils.ProofDeveloper where

import Control.Monad.Except
import Control.Monad.Operational
import Control.Monad.Reader
import Control.Monad.State









type Decomposer s e g = ProgramT g (StateT s (Either e))

class Decomposable s e g where
  decompose :: g a -> Decomposer s e g a

failure :: e -> Decomposer s e g a
failure = lift . throwError

goal :: g a -> Decomposer s e g a
goal = singleton






class Metas s g where
  substitute :: s -> g i -> g i


data Any f where
  Any :: f i -> Any f

substituteAny :: Metas s g => s -> Any g -> Any g
substituteAny s (Any g) = Any (substitute s g)

type Context a = [(Int,a)]

substituteContext :: Metas s g => s -> Context (Any g) -> Context (Any g)
substituteContext subs = map (\(i,x) -> (i, substituteAny subs x))

data ElabError s e g =
  ElabError { elabError :: e
            , elabState :: s
            , elabContext :: Context (Any g)
            , elabGoal :: Any g
            }

class ShowElabError s e g where
  showElabError :: ElabError s e g -> String



type Elaborator s e g = ReaderT (Context (Any g))
                          (StateT s
                            (Either (ElabError s e g)))

runElaborator :: Elaborator s e g a
              -> Context (Any g)
              -> s
              -> Either (ElabError s e g) (a,s)
runElaborator l ctx s =
  runStateT (runReaderT l ctx) s

throwElabError :: Metas s g => Any g -> e -> Elaborator s e g a
throwElabError g e =
  do ctx <- ask
     s <- get
     throwError
       (ElabError e
                  s
                  (substituteContext s ctx)
                  (substituteAny s g))






elaborator :: (Metas s g, Decomposable s e g) => g r -> Elaborator s e g r
elaborator g =
  do s <- get
     unroll 0 (Any g) (decompose (substitute s g))


unroll :: (Metas s g, Decomposable s e g)
        => Int -> Any g -> Decomposer s e g r -> Elaborator s e g r
unroll i upg d =
  do s <- get
     case runStateT (viewT d) s of
       Left e ->
         throwElabError upg e
       Right (pv,s') ->
         do put s'
            case pv of
              Return x ->
                return x
              g :>>= k ->
                do x <- local ((i,upg):) (elaborator g)
                   unroll (i+1) upg (k x)



chainM :: Monad m => a -> [b] -> (a -> b -> m a) -> m a
chainM x [] _ =
  return x
chainM x (y:ys) f =
  do x' <- f x y
     chainM x' ys f