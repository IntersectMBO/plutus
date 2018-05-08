{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusCore.PrettyPrint ( rewrite
                                       ) where

import           Control.Monad                  ((<=<))
import           Data.Functor.Foldable
import qualified Data.IntMap                    as IM
import           Language.PlutusCore.Identifier
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Type

-- | A monadic catamorphism
cataM :: (Recursive t, Traversable (Base t), Monad m) => (Base t a -> m a) -> (t -> m a)
cataM phi = c where c = phi <=< traverse c . project

rewrite :: (IdentifierState, Term a) -> Either ParseError (Term a)
rewrite (is, t) = g (cataM aM t) where
    aM (VarF _ (Name l (Unique i))) = PrintVar l <$> IM.lookup i (fst is)
    aM x                            = Just (embed x)
    g (Just x) = Right x
    g Nothing  = Left InternalError
