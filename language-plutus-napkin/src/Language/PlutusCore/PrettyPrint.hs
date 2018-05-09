{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusCore.PrettyPrint ( rewriteTerm
                                       ) where

import           Data.Functor.Foldable
import qualified Data.IntMap                    as IM
import           Language.PlutusCore.Identifier
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | A monadic catamorphism
cataM :: (Recursive t, Traversable (Base t), Monad m) => (Base t a -> m a) -> (t -> m a)
cataM phi = c where c = phi <=< traverse c . project

rewriteTerm :: (IdentifierState, Program a) -> Either ParseError (Program a)
rewriteTerm (is, Program l v t) = Program l v <$> g (cataM aM t) where
    aM (VarF _ (Name l' (Unique i))) = PrintVar l' <$> IM.lookup i (fst is)
    aM x                             = Just (embed x)
    g (Just x) = Right x
    g Nothing  = Left InternalError
