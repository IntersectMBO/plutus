{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Examples.Data.Rose
    (
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.MkPlc

import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Type

{- Note [Rose]
Here we encode the following:

    mutual
      data Rose (A : Set) : Set where
        node : A -> Forest A -> Rose A

      data Forest (A : Set) : Set where
        nil  : Forest A
        cons : Rose A -> Forest A -> Forest A

    mutual
      mapRose : ∀ A B -> (A -> B) -> Rose A -> Rose B
      mapRose A B f (node x forest) = node (f x) (mapForest A B f forest)

      mapForest : ∀ A B -> (A -> B) -> Forest A -> Forest B
      mapForest A B f  nil               = nil
      mapForest A B f (cons rose forest) = cons (mapRose A B f rose) (mapForest A B f forest)
-}
