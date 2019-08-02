module IOTS.Tree where

import           Control.Monad.Fix (fix)
import           Data.Foldable     (foldlM)
import           Data.Tree         (Tree (Node))

depthfirstM :: Monad m => (b -> a -> m b) -> b -> Tree a -> m b
depthfirstM f =
  fix $ \rec acc (Node root leaves)
        -- Fold the leaves first.
   -> do
    children <- foldlM rec acc leaves
        -- Deal with the root last.
    f children root
