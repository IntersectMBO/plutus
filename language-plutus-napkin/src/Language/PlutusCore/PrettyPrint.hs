{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusCore.PrettyPrint ( prettyPrint
                                       , rewrite
                                       ) where

import           Control.Monad                  ((<=<))
import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable
import qualified Data.IntMap                    as IM
import           Language.PlutusCore.Identifier
import           Language.PlutusCore.Type

-- | A monadic catamorphism
cataM :: (Recursive t, Traversable (Base t), Monad m) => (Base t a -> m a) -> (t -> m a)
cataM phi = c where c = phi <=< (traverse c . project)

rewrite :: (IdentifierState, Term a) -> Maybe (Term a)
rewrite (is, t) = cataM aM t where
    aM (VarF _ (Name l (Unique i))) = PrintVar l <$> IM.lookup i (fst is)
    aM _                            = Nothing

prettyPrint :: (IdentifierState, Term a) -> Maybe BSL.ByteString
prettyPrint (is, Var _ (Name _ (Unique i))) = IM.lookup i (fst is)
prettyPrint _                               = Nothing -- FIXME actually implement the rest
